# Requires: python-constraint
from constraint import Problem

def hm_to_min(hm):
    h, m = map(int, hm.split(":"))
    return h * 60 + m

def min_to_hm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def not_overlap_factory(blocks, duration):
    def _constraint(start):
        end = start + duration
        for b_start, b_end in blocks:
            # Overlap if intervals intersect
            if start < b_end and end > b_start:
                return False
        return True
    return _constraint

# Meeting details
day_of_week = "Monday"
duration = 30  # minutes
work_start = hm_to_min("09:00")
work_end = hm_to_min("17:00")

# Existing schedules
christine_blocks_str = [("11:00", "11:30"), ("15:00", "15:30")]
helen_blocks_str = [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")]

# Convert schedules to minutes
christine_blocks = [(hm_to_min(s), hm_to_min(e)) for s, e in christine_blocks_str]
helen_blocks = [(hm_to_min(s), hm_to_min(e)) for s, e in helen_blocks_str]

# Constraint: Helen cannot meet after 15:00 => meeting must end by 15:00
helen_end_by = hm_to_min("15:00")

# Build problem
problem = Problem()
# Start times every 30 minutes within work hours
domain = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", domain)
problem.addVariable("day", [day_of_week])

# Add constraints for no overlap with existing blocks
problem.addConstraint(not_overlap_factory(christine_blocks, duration), ["start"])
problem.addConstraint(not_overlap_factory(helen_blocks, duration), ["start"])

# Add constraint for Helen's "not after 15:00"
problem.addConstraint(lambda s: s + duration <= helen_end_by, ["start"])

# Find all feasible solutions and pick the earliest start
solutions = problem.getSolutions()
if not solutions:
    raise RuntimeError("No feasible meeting time found, but a solution was expected.")

best = min(solutions, key=lambda sol: sol["start"])
start = best["start"]
end = start + duration
time_range = f"{min_to_hm(start)}:{min_to_hm(end)}"

# Output required format:
# - Include time range in braces like {14:30:15:30}
# - Include the day of the week
print("{" + time_range + "}")
print(best["day"])