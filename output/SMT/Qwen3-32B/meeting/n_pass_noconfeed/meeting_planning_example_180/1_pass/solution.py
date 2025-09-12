from z3 import *
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

solver = Solver()

# Variables
dep_NB = Int('dep_NB')
start_james = Int('start_james')
end_james = Int('end_james')
start_robert = Int('start_robert')
end_robert = Int('end_robert')

# Constraints for James
solver.add(end_james == start_james + 75)
solver.add(start_james >= 765)
solver.add(end_james <= 840)

# Constraints for arrival at Mission
solver.add(dep_NB >= 540)
solver.add(dep_NB + 18 <= start_james)

# Constraints for Robert
solver.add(end_robert == start_robert + 30)
solver.add(start_robert >= 765)
solver.add(end_robert <= 975)

# Arrival at Castro is end_james + 7 (travel time from Mission to Castro)
solver.add(end_james + 7 <= start_robert)

# Check if satisfiable
if solver.check() == sat:
    model = solver.model()
    sj = model[start_james].as_long()
    ej = model[end_james].as_long()
    sr = model[start_robert].as_long()
    er = model[end_robert].as_long()

    itinerary = [
        {
            "action": "meet",
            "location": "Mission District",
            "person": "James",
            "start_time": to_time_str(sj),
            "end_time": to_time_str(ej)
        },
        {
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": to_time_str(sr),
            "end_time": to_time_str(er)
        }
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")