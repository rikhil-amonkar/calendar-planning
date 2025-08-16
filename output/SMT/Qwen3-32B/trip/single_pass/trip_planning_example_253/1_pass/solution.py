from z3 import *
import json

def main():
    solver = Solver()

    # Define cities as 0: Amsterdam, 1: Vienna, 2: Santorini, 3: Lyon
    s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
    solver.add(Distinct(s0, s1, s2, s3))
    for s in [s0, s1, s2, s3]:
        solver.add(And(s >= 0, s <= 3))

    # Allowed transitions
    allowed_transitions = [
        (0,2), (2,0),
        (0,3), (3,0),
        (1,0), (0,1),
        (1,2), (2,1),
        (1,3), (3,1),
    ]

    # Add constraints for consecutive transitions
    for i in range(3):
        current = [s0, s1, s2, s3][i]
        next_city = [s0, s1, s2, s3][i+1]
        constraints = []
        for a, b in allowed_transitions:
            constraints.append(And(current == a, next_city == b))
        solver.add(Or(*constraints))

    # Define durations for each city
    durations = [3,7,4,3]  # [Amsterdam, Vienna, Santorini, Lyon]

    # Compute d0, d1, d2, d3 based on the cities in the sequence
    d0 = If(s0 == 0, 3, If(s0 == 1, 7, If(s0 == 2, 4, 3)))
    d1 = If(s1 == 0, 3, If(s1 == 1, 7, If(s1 == 2, 4, 3)))
    d2 = If(s2 == 0, 3, If(s2 == 1, 7, If(s2 == 2, 4, 3)))
    d3 = If(s3 == 0, 3, If(s3 == 1, 7, If(s3 == 2, 4, 3)))

    # Compute start and end for each city in the sequence
    start_0 = 1
    end_0 = start_0 + d0 - 1

    start_1 = end_0
    end_1 = start_1 + d1 - 1

    start_2 = end_1
    end_2 = start_2 + d2 - 1

    start_3 = end_2
    end_3 = start_3 + d3 - 1

    # Add event constraints
    for i, (city, start, end) in enumerate(zip([s0, s1, s2, s3], 
                                               [start_0, start_1, start_2, start_3],
                                               [end_0, end_1, end_2, end_3])):
        # Check if city is Lyon (3)
        solver.add(Implies(city == 3, And(start <= 9, end >=7)))
        # Check if city is Amsterdam (0)
        solver.add(Implies(city == 0, And(start <= 11, end >=9)))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract sequence
        sequence = [model.eval(s0).as_long(), model.eval(s1).as_long(), model.eval(s2).as_long(), model.eval(s3).as_long()]
        # Compute durations for each city in the sequence
        d0_val = durations[sequence[0]]
        d1_val = durations[sequence[1]]
        d2_val = durations[sequence[2]]
        d3_val = durations[sequence[3]]
        # Compute start and end days
        start_0_val = 1
        end_0_val = start_0_val + d0_val - 1

        start_1_val = end_0_val
        end_1_val = start_1_val + d1_val - 1

        start_2_val = end_1_val
        end_2_val = start_2_val + d2_val - 1

        start_3_val = end_2_val
        end_3_val = start_3_val + d3_val - 1

        # Generate itinerary
        city_names = {0: 'Amsterdam', 1: 'Vienna', 2: 'Santorini', 3: 'Lyon'}
        itinerary = []
        for i in range(4):
            city_idx = sequence[i]
            start_day = [start_0_val, start_1_val, start_2_val, start_3_val][i]
            end_day = [end_0_val, end_1_val, end_2_val, end_3_val][i]
            city_name = city_names[city_idx]
            for day in range(start_day, end_day + 1):
                itinerary.append({'day': day, 'city': city_name})

        # Sort itinerary by day (though it should already be in order)
        itinerary.sort(key=lambda x: x['day'])

        # Output JSON
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()