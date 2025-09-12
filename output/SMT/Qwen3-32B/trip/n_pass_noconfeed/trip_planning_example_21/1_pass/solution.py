import json
from z3 import *

def main():
    solver = Solver()

    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')

    # All cities are distinct and in 0,1,2
    solver.add(And([s1 >= 0, s1 <= 2]))
    solver.add(And([s2 >= 0, s2 <= 2]))
    solver.add(And([s3 >= 0, s3 <= 2]))
    solver.add(Distinct(s1, s2, s3))

    # Allowed transitions between consecutive cities
    allowed_transitions = [(0, 1), (1, 0), (1, 2), (2, 1)]

    # Check transitions between s1 and s2
    transitions_s1s2 = [And(s1 == a, s2 == b) for a, b in allowed_transitions]
    solver.add(Or(transitions_s1s2))

    # Check transitions between s2 and s3
    transitions_s2s3 = [And(s2 == a, s3 == b) for a, b in allowed_transitions]
    solver.add(Or(transitions_s2s3))

    # Compute durations for each segment
    d1 = If(s1 == 0, 2, If(s1 == 1, 4, 6))
    d2 = If(s2 == 0, 2, If(s2 == 1, 4, 6))
    d3 = If(s3 == 0, 2, If(s3 == 1, 4, 6))

    # Compute end days
    seg1_end = d1
    seg2_end = seg1_end + d2 - 1
    seg3_end = seg2_end + d3 - 1

    # The third segment must end on day 10
    solver.add(seg3_end == 10)

    # Now check if the model is satisfiable
    if solver.check() == sat:
        model = solver.model()
        order = [model[s1].as_long(), model[s2].as_long(), model[s3].as_long()]
        cities = {0: 'Mykonos', 1: 'Vienna', 2: 'Venice'}
        segments = []
        current_start = 1
        for city_id in order:
            duration = 2 if city_id == 0 else 4 if city_id == 1 else 6
            end = current_start + duration - 1
            city_name = cities[city_id]
            segments.append({
                'start': current_start,
                'end': end,
                'city': city_name
            })
            current_start = end  # next segment starts at this end

        # Build the itinerary JSON
        itinerary = []
        for seg in segments:
            day_range = f"Day {seg['start']}-{seg['end']}"
            itinerary.append({'day_range': day_range, 'place': seg['city']})

        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()