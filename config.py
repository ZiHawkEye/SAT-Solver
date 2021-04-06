class PickBranchHeuristics:
    FIRST_VARIABLE = "next_smallest_literal"
    RANDOM = "random"
    GREEDY = "greedy"
    VSIDS = "vsids"


class ConflictAnalysisHeuristics:
    GRASP = "grasp"
    ONE_UIP = "1-uip"

class VSIDSConfig:
    CONFLICT_BUMP = 1 # Additive score to literal
    MULTIPLICATIVE_DECAY_FACTOR = 2 # Multiplicative factor to divide scores after DECAY_TIME conflicts
    DECAY_TIME = 256 # Number of conflicts needed for every decay.

class Config:
    pick_branch_heuristic = PickBranchHeuristics.VSIDS
    conflict_analysis_heuristic = ConflictAnalysisHeuristics.ONE_UIP
    test_case = "uuf150-01.cnf"
    num_of_times_to_run = 5