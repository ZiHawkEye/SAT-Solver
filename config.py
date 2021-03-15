class PickBranchHeuristics:
    FIRST_VARIABLE = "first_variable"
    RANDOM = "random"
    GREEDY = "greedy"


class ConflictAnalysisHeuristics:
    GRASP = "grasp"
    ONE_UIP = "1-uip"


class Config:
    pick_branch_heuristic = PickBranchHeuristics.GREEDY
    conflict_analysis_heuristic = ConflictAnalysisHeuristics.ONE_UIP
    test_case = "test_case_7.txt"