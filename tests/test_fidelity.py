"""Offline regressions against independently generated, pinned C results."""
import unittest
import subprocess
import fidelity_reference as reference


class FidelityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.golden = reference.checked_golden()
        cls.cases = reference.corpus()

    def check_group(self, name):
        commands = self.cases[name]
        reference.compare(commands, self.golden["groups"][name]["expected"],
                          reference.run_probe(reference.probe_for(name), commands), name)

    def test_imp_actions(self):
        self.check_group("imp_actions")

    def test_imp_chase(self):
        self.check_group("imp_chase")

    def test_imp_sequences(self):
        self.check_group("imp_sequences")

    def test_imp_projectile_spawn(self):
        self.check_group("imp_projectile_spawn")

    def test_imp_missile_collision(self):
        self.check_group("imp_missile_collision")

    def test_death_imp_barrel(self):
        self.check_group("death_imp_barrel")

    def test_sight_side(self):
        self.check_group("sight_side")

    def test_sight_portals(self):
        self.check_group("sight_portals")

    def test_radius_falloff(self):
        self.check_group("radius_falloff")

    def test_radius_blocks(self):
        self.check_group("radius_blocks")

    def test_death_kills(self):
        self.check_group("death_kills")

    def test_death_sequences(self):
        self.check_group("death_sequences")

    def test_hitscan_autoaim(self):
        self.check_group("hitscan_aim")

    def test_hitscan_shots(self):
        self.check_group("hitscan_shots")

    def test_secret_sectors(self):
        self.check_group("secret_sectors")

    def test_exit_switches(self):
        self.check_group("exit_switches")

    def test_original_switch_palette(self):
        self.check_group("switch_palette")

    def test_wrapping_add(self):
        self.check_group("add")

    def test_wrapping_sub(self):
        self.check_group("sub")

    def test_fixed_multiply(self):
        self.check_group("mul")

    def test_raw_bsp_side(self):
        self.check_group("side")

    def test_map_node_integration(self):
        self.check_group("node")

    def test_random_streams_and_reset(self):
        self.check_group("random")

    def test_saturating_division_verified_domain(self):
        self.check_group("div")

    def test_all_table_entries(self):
        self.check_group("tables")

    def test_every_fine_angle_bin(self):
        self.check_group("fine")

    def test_unsigned_slope_division(self):
        self.check_group("slope")

    def test_point_to_angle(self):
        self.check_group("angle")

    def test_keyboard_commands(self):
        self.check_group("keyboard")

    def test_thrust_all_fine_angles(self):
        self.check_group("thrust")

    def test_player_command_order_and_grounding(self):
        self.check_group("move_player")

    def test_xy_splits_and_friction(self):
        self.check_group("xy_movement")

    def test_unobstructed_momentum_traces(self):
        self.check_group("motion_traces")

    def test_gravity_floor_ceiling_and_landing(self):
        self.check_group("z_movement")

    def test_view_bob_recovery_and_airborne_quirk(self):
        self.check_group("view_height")

    def test_ordered_unobstructed_player_physics(self):
        self.check_group("physics_traces")

    def test_collision_point_box_and_block_coordinates(self):
        self.check_group("collision_geometry")

    def test_ordered_player_position_checks(self):
        self.check_group("collision_positions")

    def test_try_move_guards_and_commit(self):
        self.check_group("try_move")

    def test_actor_relink_order(self):
        self.check_group("move_links")

    def test_crossed_special_callback_order(self):
        self.check_group("move_specials")

    def test_divline_sides_and_intercept_fractions(self):
        self.check_group("path_arithmetic")

    def test_ordered_path_traversal(self):
        self.check_group("path_traversal")

    def test_fixed_slide_projection(self):
        self.check_group("slide_projection")

    def test_three_corner_slide_and_fallback(self):
        self.check_group("slide_movement")

    def test_connected_xy_collision_slide_and_friction(self):
        self.check_group("world_xy")

    def test_connected_player_movement_traces(self):
        self.check_group("world_physics")

    def test_runtime_bridge_reference(self):
        self.check_group("walking_bridge")

    def test_pickup_contacts_commit_before_move_rejection(self):
        self.check_group("pickup_contacts")

    def test_pickups_during_connected_movement(self):
        self.check_group("pickup_movement")

    def test_original_sector_light_spawns(self):
        self.check_group("light_spawns")

    def test_original_sector_light_sequences(self):
        self.check_group("light_sequences")

    def test_original_sector_light_rng_and_thinker_order(self):
        self.check_group("light_order")

    def test_original_walkover_light_actions(self):
        self.check_group("light_triggers")
        self.check_group("light_trigger_sequences")

    def test_original_plane_steps(self):
        self.check_group("plane_steps")

    def test_original_height_clipping(self):
        self.check_group("height_clip")

    def test_original_height_clipping_with_position_and_pickup_effects(self):
        self.check_group("height_clip_positions")

    def test_original_turbo_floor_thinker(self):
        self.check_group("floor_mover_steps")

    def test_original_down_wait_up_stay_thinker(self):
        self.check_group("lift_mover_steps")

    def test_original_e1m1_mover_spawns_and_triggers(self):
        self.check_group("e1m1_mover_spawns")

    def test_active_platform_limit_is_explicit(self):
        commands=["reset"]+["sector 0 128 7 0"]*31+["line 0 0 -1 88 7","cross 0 1 0 0"]
        with self.assertRaises(subprocess.CalledProcessError) as error:
            reference.run_probe(reference.probe_for("e1m1_mover_spawns"),commands)
        self.assertIn("MAXPLATS=30",error.exception.stderr)

    def test_original_use_lines(self):
        self.check_group("use_lines")

    def test_original_scrolling_wall_sequences(self):
        self.check_group("wall_scrolling")

    def test_scrolling_list_rejects_overflow(self):
        commands=["scrollreset","scrollside 0"]+["scrollline 48 0"]*65+["scrollspawn"]
        with self.assertRaises(subprocess.CalledProcessError) as error:
            reference.run_probe(reference.probe_for("wall_scrolling"),commands)
        self.assertIn("more than 64",error.exception.stderr)

    def test_original_sector_bounds(self):
        self.check_group("sector_bounds")

    def test_original_noncrushing_sector_changes(self):
        self.check_group("sector_changes")

    def test_original_actor_sector_flags(self):
        self.check_group("actor_flags")

    def test_original_door_steps(self):
        self.check_group("door_steps")

    def test_original_door_sequences(self):
        self.check_group("door_sequences")
        self.check_group("door_runtime")

    def test_door_probe_rejects_invalid_inputs(self):
        for command in ("plane 0 0 -1 0 0 1 1 0", "plane 0 0 1 0 2 1 1 0",
                        "plane 0 0 1 0 0 2 1 0", "plane 0 0 1 0 0 1 0 0",
                        "door 8 0 0 1 2 1 150 0", "door 0 0 0 1 2 3 150 0",
                        "plane 2147483648 0 1 0 0 1 1 0", "tick 0"):
            with self.subTest(command=command):
                with self.assertRaises(subprocess.CalledProcessError):
                    reference.run_probe(reference.probe_for("plane_steps"), [command])

    def test_light_probe_rejects_invalid_map_setup(self):
        for commands in (["sector 32768 1"], ["reset 256 0"], ["sector 128 1", "line 4 0 -1"],
                         ["sector 128 1", "spawn", "spawn"], ["tick"]):
            with self.subTest(commands=commands):
                with self.assertRaises(subprocess.CalledProcessError):
                    reference.run_probe(reference.probe_for("light_spawns"), commands)

    def test_original_status_numbers(self):
        self.check_group("status_numbers")

    def test_original_status_palette_selection(self):
        self.check_group("status_palettes")

    def test_original_status_face_sequences(self):
        self.check_group("status_faces")

    def test_original_status_weapon_and_key_selection(self):
        self.check_group("status_widgets")

    def test_status_probe_rejects_invalid_inputs(self):
        for command in ("face -1 0 0 0 3 0 0 0 -1 0", "face 100 0 0 0 3 0 0 0 -1 256",
                        "widgets 9 0 1 2 3 4", "num 100 1 8", "palette -1 0 0 0", "start 512"):
            with self.subTest(command=command):
                with self.assertRaises(subprocess.CalledProcessError):
                    reference.run_probe(reference.probe_for("status_faces"), [command])

    def test_original_fuzz_columns(self):
        self.check_group("fuzz_columns")

    def test_stateful_fuzz_posts_and_frames(self):
        self.check_group("fuzz_sequences")

    def test_fuzz_rejects_unsupported_bounds(self):
        for command in ("draw 320 0 199 200", "draw 0 -1 1 200", "draw 0 0 200 200",
                        "draw 0 0 0 2", "reset 0 50 0"):
            with self.subTest(command=command):
                with self.assertRaises(subprocess.CalledProcessError):
                    reference.run_probe(reference.probe_for("fuzz_columns"), [command])

    def test_original_render_colormap_selection(self):
        self.check_group("render_colormaps")

    def test_player_counter_stage(self):
        self.check_group("player_counters")

    def test_power_expiry_and_repeated_pickup_sequences(self):
        self.check_group("power_sequences")

    def test_pickup_editor_metadata(self):
        self.check_group("pickup_metadata")

    def test_original_pickup_grant_rules(self):
        self.check_group("pickup_grants")

    def test_pickup_height_effects_and_events(self):
        self.check_group("pickup_touch")

    def test_stateful_pickup_sequences(self):
        self.check_group("pickup_sequences")

    def test_pickup_fixture_rejects_invalid_enums(self):
        probe = reference.probe_for("pickup_touch")
        for command in ("giveammo -1 1", "giveammo 5 1", "giveweapon 9 0",
                        "givecard 6", "givepower 6", "touch 36 0 0 3670016 0 0",
                        "profile 5 1", "profile 2 2", "givebody 2147483648"):
            with self.subTest(command=command):
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    reference.run_probe(probe,[command])
                self.assertIn("integer outside",error.exception.stderr)

    def test_motion_fixture_rejects_invalid_widths(self):
        for command in ("move 128 0 0", "move 0 -129 0", "move 0 0 32768",
                        "body 2147483648 0 0 0 0 0 0 0 0", "key 1024 1",
                        "key 0 0", "body 0 0 0 0 0 0 0 5 0"):
            with self.subTest(command=command):
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    reference.run_probe(reference.probe_for("keyboard"), [command])
                self.assertIn("integer outside", error.exception.stderr)

    def test_division_preserves_original_dos_minimum_integer_outcomes(self):
        # Original 1.9 instructions, not undefined abs(INT_MIN) in the C oracle.
        commands = [f"div {a} {b}" for a, b in [(-2147483648, 0), (-2147483648, 1),
                    (-2147483648, -2147483648), (1, -2147483648), (0, -2147483648),
                    (-2147483648, 65536), (-2147483648, -65536), (-2147483648, -65537)]]
        self.assertEqual(reference.run_probe(reference.PROBE, commands),
                         ["divide-by-zero", "quotient-overflow", "2147483647", "-2147483648",
                          "-2147483648", "-2147483648", "quotient-overflow", "2147450880"])
