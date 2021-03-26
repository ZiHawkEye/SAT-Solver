class PickBranchHeuristics:
    FIRST_VARIABLE = "next_smallest_literal"
    RANDOM = "random"
    GREEDY = "greedy"


class ConflictAnalysisHeuristics:
    GRASP = "grasp"
    ONE_UIP = "1-uip"


class Config:
    pick_branch_heuristic = PickBranchHeuristics.GREEDY
    conflict_analysis_heuristic = ConflictAnalysisHeuristics.ONE_UIP
    test_case = "test_case_4.txt"
    num_of_times_to_run = 1