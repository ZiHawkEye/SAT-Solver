"""
Contains settings for SAT solver.
"""
class Config:
    IS_LOG = False

    IS_VSIDS = True
    VSIDS_INTERVAL = 256

    IS_RESTART = False
    RESTART_INTERVAL = 256
    RESTART_MULTIPLIER = 2
    
    IS_PROOF = True
    OUTPUT_PATH = "proof.txt"