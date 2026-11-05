import BlockGeometry
import CloseBlocks
import CloseGeometry
import CloseTransition
import CofiniteCounting
import CofiniteGlobal
import CofiniteResults
import EntranceBlocks
import EntranceBridge
import EntranceExamples
import EntranceGlobal
import EntranceResults
import EntranceTrace
import Examples
import FinitePrefix
import Global
import History
import HoleCount
import InfiniteWitnesses
import LaneExamples
import LaneFill
import LaneLiteral
import LaneStep
import MixedBlocks
import MixedGeometry
import MixedGlobal
import OneSide
import OriginalRule
import RepairBlocks
import RepairEntrance
import RepairGlobal
import ResidueAlgebra
import ResidueCoverage
import ResidueOmission
import ResidueResults
import Semantics
import Shielded
import TripleBlocks
import TripleGlobal
import TripleObstruction
import UniversalGlobal
import UniversalLiteral
import UniversalTransition

#print axioms G01.Reaches.trans
#print axioms G01.active_min_greedy
#print axioms G01.allowed_eq
#print axioms G01.descent_finish
#print axioms G01.descent_step
#print axioms G01.difference_symm
#print axioms G01.entranceState_spec
#print axioms G01.entrance_frame
#print axioms G01.fill_finish
#print axioms G01.fill_step
#print axioms G01.frame_visit
#print axioms G01.greedy_exists
#print axioms G01.greedy_unique
#print axioms G01.historyList_mem
#print axioms G01.history_succ
#print axioms G01.history_zero
#print axioms G01.initial_positive
#print axioms G01.interval_visit_left
#print axioms G01.interval_visit_right
#print axioms G01.least_nat
#print axioms G01.map_nodup_injective
#print axioms G01.next_positive
#print axioms G01.one_side_filling
#print axioms G01.opposite_disjoint
#print axioms G01.point_abs
#print axioms G01.point_add_distance
#print axioms G01.point_cases
#print axioms G01.point_injective
#print axioms G01.point_sub_distance
#print axioms G01.rank_order
#print axioms G01.reaches_history
#print axioms G01.second_negative
#print axioms G01.sparse_descent_visit
#print axioms G01.state_ext
#print axioms G01.unused_active
#print axioms G01.visit_bounded
#print axioms G01.walk_injective
#print axioms G01.zero_bounded
#print axioms G02.certificate_from_zero
#print axioms G02.certificate_history
#print axioms G02.finite_greedy_sound
#print axioms G02.mem_candidates
#print axioms G02.next_spec
#print axioms G02.orbit_history
#print axioms G02.unbounded_admissible
#print axioms G02.unbounded_exists
#print axioms G03.boxList_mem
#print axioms G03.box_history_index
#print axioms G03.cross_positive
#print axioms G03.fill_negative
#print axioms G03.fill_positive
#print axioms G03.inside_greedy
#print axioms G03.inside_visit
#print axioms G03.negative_run
#print axioms G03.negative_step
#print axioms G03.odd_next
#print axioms G03.reached_box
#print axioms G03.reaches_used
#print axioms G03.shielded_filling
#print axioms G03.transfer_inside
#print axioms G05.cross_negative
#print axioms G05.even_boundary_positive
#print axioms G05.fill_negative_closed
#print axioms G05.fill_positive_closed
#print axioms G05.negative_block
#print axioms G05.odd_boundary_negative
#print axioms G05.positive_block
#print axioms G05.positive_run
#print axioms G05.positive_step
#print axioms G06.adjacent_transition
#print axioms G06.all_checkpoints
#print axioms G06.allowed_of_unused
#print axioms G06.completion_coverage
#print axioms G06.completion_exists
#print axioms G06.completion_unbounded
#print axioms G06.every_distance
#print axioms G06.initial_checkpoint
#print axioms G06.literal_checkpoints
#print axioms G06.literal_coverage
#print axioms G06.literal_exists
#print axioms G06.literal_iff
#print axioms G06.nextDistance_spec
#print axioms G06.scale_checkpoints
#print axioms G06.scales_growth
#print axioms G06.scales_member
#print axioms G06.separated_transition
#print axioms G06.transition
#print axioms G06.unbounded_coverage
#print axioms G06.unbounded_exists
#print axioms G07.block_certificate
#print axioms G07.block_finish
#print axioms G07.blocked_no_completion
#print axioms G07.blocked_no_interior
#print axioms G07.blocked_used
#print axioms G07.certificate_prevents_completion
#print axioms G07.cross_negative
#print axioms G07.family_blocks
#print axioms G07.family_checkpoints
#print axioms G07.family_coverage
#print axioms G07.family_unbounded
#print axioms G07.finish_preserves_used
#print axioms G07.finite_of_greedy
#print axioms G07.initial_box
#print axioms G07.initial_certificate
#print axioms G07.initial_history
#print axioms G07.inward_certificate
#print axioms G07.literal_checkpoints
#print axioms G07.literal_coverage
#print axioms G07.literal_exists
#print axioms G07.local_filling_impossible
#print axioms G07.next_positive
#print axioms G07.optional_family
#print axioms G07.optional_result
#print axioms G07.reaches_used
#print axioms G07.reference_family
#print axioms G07.repair_negative
#print axioms G07.same_rule_global_coverage
#print axioms G07.second_positive
#print axioms G08.absent_two_counterexample
#print axioms G08.canonical_literal
#print axioms G08.conditional_lane_filling
#print axioms G08.extra_even_counterexample
#print axioms G08.extra_hole_counterexample
#print axioms G08.finite_literal_prefix
#print axioms G08.finite_visit
#print axioms G08.history_segment
#print axioms G08.interior_current_used
#print axioms G08.interior_visit
#print axioms G08.inward_greedy
#print axioms G08.lane_count
#print axioms G08.literal_iff
#print axioms G08.literal_state_eq
#print axioms G08.literal_walk_lane
#print axioms G08.negative_exterior_filling
#print axioms G08.point_distance
#print axioms G08.positive_exterior_filling
#print axioms G08.prefix_current_used
#print axioms G08.prefix_next
#print axioms G08.prefix_run
#print axioms G08.prefix_zero
#print axioms G08.run_complete_iff
#print axioms G08.run_current
#print axioms G08.run_finite
#print axioms G08.run_greedy
#print axioms G08.run_interior
#print axioms G08.run_used
#print axioms G08.sample_distances
#print axioms G08.sample_entry
#print axioms G08.sample_exterior
#print axioms G08.sample_filling
#print axioms G08.sample_finite
#print axioms G08.state_ext
#print axioms G08.third_inward_move_counterexample
#print axioms G08.two_holes
#print axioms G08.unused_distance_positive
#print axioms G08.walk_segment_literal
#print axioms G08.wrong_entrance_counterexample
#print axioms G08E.abs_distance_bound
#print axioms G08E.actual_block_states
#print axioms G08E.actual_box
#print axioms G08E.actual_entrance
#print axioms G08E.actual_hole_count
#print axioms G08E.actual_hole_enumeration
#print axioms G08E.altered_threshold_breaks_short_choice
#print axioms G08E.altered_threshold_competitor
#print axioms G08E.base_large
#print axioms G08E.base_short
#print axioms G08E.base_state
#print axioms G08E.block_large
#print axioms G08E.block_short
#print axioms G08E.block_state
#print axioms G08E.boundary_one
#print axioms G08E.boundary_previous_index
#print axioms G08E.boundary_two
#print axioms G08E.box_deadline
#print axioms G08E.difference_symmetric
#print axioms G08E.endpoint_minus_seven_used
#print axioms G08E.entrance_hole_inside
#print axioms G08E.every_entrance_hole_repaired
#print axioms G08E.exact_entrance
#print axioms G08E.final_jump
#print axioms G08E.final_state
#print axioms G08E.follow_trace
#print axioms G08E.front_large
#print axioms G08E.front_short
#print axioms G08E.front_state
#print axioms G08E.history_next
#print axioms G08E.history_zero
#print axioms G08E.lift_trace
#print axioms G08E.literal_exists
#print axioms G08E.literal_rule_iff
#print axioms G08E.negative_preferred
#print axioms G08E.negative_shield
#print axioms G08E.no_uniform_hole_bound
#print axioms G08E.omitted_entrance_deadline
#print axioms G08E.positive_preferred
#print axioms G08E.short_greedy
#print axioms G08E.short_lift
#print axioms G08E.short_signed
#print axioms G08E.unbounded_reachable_holes
#print axioms G08E.walk_greedy
#print axioms G08H.holesList_length
#print axioms G08H.holesList_mem_formula
#print axioms G08H.holesList_mem_iff
#print axioms G08H.holesList_nodup
#print axioms G08H.holes_five
#print axioms G08H.holes_ten
#print axioms G08H.lane_hole_iff
#print axioms G08H.map_injective_nodup
#print axioms G09.after_repair
#print axioms G09.certificate_take
#print axioms G09.checkpoints
#print axioms G09.coverage
#print axioms G09.cross_after_three
#print axioms G09.distances_unbounded
#print axioms G09.entrance_certificate
#print axioms G09.entrance_frontier
#print axioms G09.entrance_history
#print axioms G09.first_checkpoint_frame
#print axioms G09.first_repair
#print axioms G09.forward_three
#print axioms G09.immediate_repairs
#print axioms G09.last_negative
#print axioms G09.literal_checkpoints
#print axioms G09.literal_coverage
#print axioms G09.literal_exists
#print axioms G09.literal_repair_bound
#print axioms G09.literal_repairs
#print axioms G09.original_hole
#print axioms G09.repair_certificate
#print axioms G09.repair_finish
#print axioms G09.repairs_within_three
#print axioms G09.second_checkpoint_frame
#print axioms G09.second_hole
#print axioms G09.tail_hypotheses
#print axioms G10.g08_box_deadline
#print axioms G10.g08_exists
#print axioms G10.g08_odd_tail
#print axioms G10.lane_point_injective
#print axioms G10.lane_point_properties
#print axioms G10.length_le_code
#print axioms G10.literal_coverage
#print axioms G10.literal_exists
#print axioms G10.literal_first_visit
#print axioms G10.literal_first_visit_unique
#print axioms G10.literal_unique
#print axioms G10.map_nodup_on
#print axioms G10.missing_forces_small
#print axioms G10.missing_target_count
#print axioms G10.near_code_bound
#print axioms G10.near_code_injective
#print axioms G10.odd_tail_unbounded
#print axioms G10.omission_bound
#print axioms G10.opposite_mem
#print axioms G10.opposite_prefix
#print axioms G10.parity_distance
#print axioms G10.parity_partition
#print axioms G10.second_missing
#print axioms G18.all_omitted_classes
#print axioms G18.class_above
#print axioms G18.class_below
#print axioms G18.class_difference
#print axioms G18.duplicate_residues_exists
#print axioms G18.eventually_ne
#print axioms G18.eventually_outside
#print axioms G18.finite_class_bound
#print axioms G18.finite_eventually
#print axioms G18.literal_coverage
#print axioms G18.literal_exists
#print axioms G18.lower_class
#print axioms G18.missing_avoids
#print axioms G18.mixed_six_exists
#print axioms G18.mixed_six_residues
#print axioms G18.modulus_one_exists
#print axioms G18.odd_tail_coverage
#print axioms G18.omitted_add
#print axioms G18.omitted_period
#print axioms G18.omitted_shift
#print axioms G18.omitted_sub
#print axioms G18.positive_distance_mod
#print axioms G18.prefix_bound
#print axioms G18.progression_exists
#print axioms G18.progression_five_exists
#print axioms G18.progression_five_no_short
#print axioms G18.shift_add
#print axioms G18.shift_fold_gcd
#print axioms G18.shift_gcd
#print axioms G18.shift_int_mul
#print axioms G18.shift_mod
#print axioms G18.shift_nat_mul
#print axioms G18.shift_neg
#print axioms G18.shift_one_all
#print axioms G18.shift_zero
#print axioms G18.tail_unbounded
#print axioms G18.upper_class
#print axioms G18.visited_class_bounded
