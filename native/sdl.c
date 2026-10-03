#define SDL_MAIN_HANDLED
#include <SDL.h>
#include <lean/lean.h>

/* Device I/O only. Lean owns the camera, BSP traversal, and RGB framebuffer. */
static SDL_Window *window;
static SDL_Renderer *renderer;
static SDL_Texture *texture;
static SDL_AudioDeviceID audio_device;
static uint32_t frame_width, frame_height;

/* Only Viewer.c substitutes its generated call to lean_run_main with this.
 * The generated entry point still initializes/finalizes the Lean runtime.
 * Running the Lean IO loop here keeps all Cocoa/SDL calls on the OS main thread.
 */
LEAN_EXPORT lean_obj_res doom_run_on_main(lean_object *(*main_fn)(int, char **),
                                         int argc, char **argv) {
    return main_fn(argc, argv);
}

static void cleanup(void) {
    if (audio_device) SDL_CloseAudioDevice(audio_device);
    audio_device = 0;
    if (texture) SDL_DestroyTexture(texture);
    if (renderer) SDL_DestroyRenderer(renderer);
    if (window) SDL_DestroyWindow(window);
    texture = NULL;
    renderer = NULL;
    window = NULL;
    SDL_Quit();
}

static lean_obj_res fail(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

static lean_obj_res init_failed(void) {
    lean_object *result = fail(SDL_GetError());
    cleanup();
    return result;
}

LEAN_EXPORT lean_obj_res doom_window_open(uint32_t width, uint32_t height) {
    if (window) return fail("window already open");
    if (!width || !height || width > 4096 || height > 4096)
        return fail("invalid framebuffer dimensions");
    SDL_SetMainReady();
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_TIMER) != 0) return init_failed();
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "0");
    window = SDL_CreateWindow("Lean DOOM | Walk / F free camera | WASD / arrows / R / Esc",
        SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
        (int)width * 3, (int)height * 3, SDL_WINDOW_RESIZABLE | SDL_WINDOW_ALLOW_HIGHDPI);
    if (!window) return init_failed();
    renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
    if (!renderer) renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_SOFTWARE);
    if (!renderer) return init_failed();
    if (SDL_RenderSetLogicalSize(renderer, (int)width, (int)height) != 0) return init_failed();
    texture = SDL_CreateTexture(renderer, SDL_PIXELFORMAT_RGB24,
        SDL_TEXTUREACCESS_STREAMING, (int)width, (int)height);
    if (!texture) return init_failed();
    frame_width = width;
    frame_height = height;
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res doom_window_title(b_lean_obj_arg title) {
    if (!window) return fail("window is not open");
    SDL_SetWindowTitle(window, lean_string_cstr(title));
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res doom_window_close(void) {
    cleanup();
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res doom_window_poll(void) {
    if (!window) return fail("window is not open");
    SDL_Event event;
    uint32_t bits = 0;
    while (SDL_PollEvent(&event)) {
        if (event.type == SDL_QUIT ||
            (event.type == SDL_WINDOWEVENT && event.window.event == SDL_WINDOWEVENT_CLOSE)) bits |= 1;
    }
    const Uint8 *keys = SDL_GetKeyboardState(NULL);
    if (SDL_GetKeyboardFocus() == window) {
        if (keys[SDL_SCANCODE_ESCAPE]) bits |= 1;
        if (keys[SDL_SCANCODE_W] || keys[SDL_SCANCODE_UP]) bits |= 2;
        if (keys[SDL_SCANCODE_S] || keys[SDL_SCANCODE_DOWN]) bits |= 4;
        if (keys[SDL_SCANCODE_A]) bits |= 8;
        if (keys[SDL_SCANCODE_D]) bits |= 16;
        if (keys[SDL_SCANCODE_LEFT]) bits |= 32;
        if (keys[SDL_SCANCODE_RIGHT]) bits |= 64;
        if (keys[SDL_SCANCODE_E]) bits |= 128;
        if (keys[SDL_SCANCODE_Q]) bits |= 256;
        if (keys[SDL_SCANCODE_LSHIFT] || keys[SDL_SCANCODE_RSHIFT]) bits |= 512;
        if (keys[SDL_SCANCODE_R]) bits |= 1024;
        if (keys[SDL_SCANCODE_F]) bits |= 2048;
        if (keys[SDL_SCANCODE_SPACE]) bits |= 4096;
        if (keys[SDL_SCANCODE_1]) bits |= 16384;
        if (keys[SDL_SCANCODE_2]) bits |= 32768;
        if (keys[SDL_SCANCODE_3]) bits |= 65536;
        if (keys[SDL_SCANCODE_LCTRL] || keys[SDL_SCANCODE_RCTRL] ||
            (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON(SDL_BUTTON_LEFT))) bits |= 8192;
    }
    return lean_io_result_mk_ok(lean_box_uint32(bits));
}

LEAN_EXPORT lean_obj_res doom_window_present(b_lean_obj_arg pixels) {
    if (!texture) return fail("window is not open");
    if (lean_sarray_size(pixels) != (size_t)frame_width * frame_height * 3)
        return fail("RGB framebuffer size does not match window");
    if (SDL_UpdateTexture(texture, NULL, lean_sarray_cptr(pixels), (int)frame_width * 3) != 0)
        return fail(SDL_GetError());
    if (SDL_RenderClear(renderer) != 0 || SDL_RenderCopy(renderer, texture, NULL, NULL) != 0)
        return fail(SDL_GetError());
    SDL_RenderPresent(renderer);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res doom_window_seconds(void) {
    double seconds = (double)SDL_GetPerformanceCounter() / (double)SDL_GetPerformanceFrequency();
    return lean_io_result_mk_ok(lean_box_float(seconds));
}

/* Lean supplies interleaved signed 16-bit little-endian stereo at 44,100 Hz. */
LEAN_EXPORT lean_obj_res doom_audio_open(void) {
    if (!window) return fail("audio requires an open platform session");
    if (audio_device) return fail("audio already open");
    if (SDL_InitSubSystem(SDL_INIT_AUDIO) != 0) return fail(SDL_GetError());
    SDL_AudioSpec wanted = {0}, obtained;
    wanted.freq = 44100; wanted.format = AUDIO_S16LSB;
    wanted.channels = 2; wanted.samples = 1024;
    audio_device = SDL_OpenAudioDevice(NULL, 0, &wanted, &obtained, 0);
    if (!audio_device) return fail(SDL_GetError());
    SDL_PauseAudioDevice(audio_device, 0);
    return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res doom_audio_queue(b_lean_obj_arg pcm) {
    if (!audio_device) return fail("audio is not open");
    size_t len = lean_sarray_size(pcm);
    if (len % 4 || len > 44100*4) return fail("invalid stereo PCM block");
    /* No silent dropping: report runaway production instead of growing forever. */
    if (SDL_GetQueuedAudioSize(audio_device) + len > 44100*4)
        return fail("audio queue exceeds one second");
    if (SDL_QueueAudio(audio_device, lean_sarray_cptr(pcm), (Uint32)len) != 0)
        return fail(SDL_GetError());
    return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res doom_audio_clear(void) {
    if (!audio_device) return fail("audio is not open");
    SDL_ClearQueuedAudio(audio_device);
    return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res doom_audio_queued(void) {
    if (!audio_device) return fail("audio is not open");
    return lean_io_result_mk_ok(lean_box_uint32(SDL_GetQueuedAudioSize(audio_device)));
}
