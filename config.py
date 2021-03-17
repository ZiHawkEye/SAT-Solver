class PickBranchHeuristics:
    FIRST_VARIABLE = "next_smallest_literal"
    RANDOM = "random"
    GREEDY = "greedy"


class ConflictAnalysisHeuristics:
    GRASP = "grasp"
    ONE_UIP = "1-uip"


class Config:
    pick_branch_heuristic = PickBranchHeuristics.RANDOM
    conflict_analysis_heuristic = ConflictAnalysisHeuristics.ONE_UIP
    test_case = "einstein.cnf"
    num_of_times_to_run = 1
