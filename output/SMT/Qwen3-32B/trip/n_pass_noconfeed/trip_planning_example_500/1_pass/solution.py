from z3 import *
import json

def main():
    s = Solver()

    # Define order variables: order_0 to order_4
    order = [Int(f'order_{i}') for i in range(5)]
    cities = [0, 1, 2, 3, 4]  # 0:Hamburg, 1:Munich, 2:Manchester, 3:Lyon, 4:Split

    # All order variables are distinct and in 0-4
    s.add(Distinct(order))
    for o in order:
        s.add(And(o >= 0, o <= 4))

    # Allowed transitions
    allowed_transitions = {
        (0, 1), (1, 0),  # Hamburg-Munich
        (0, 2), (2, 0),  # Hamburg-Manchester
        (0, 4), (4, 0),  # Hamburg-Split
        (1, 2), (2, 1),  # Munich-Manchester
        (1, 4), (4, 1),  # Munich-Split
        (1, 3), (3, 1),  # Munich-Lyon
        (3, 4), (4, 3),  # Lyon-Split
        (2, 4),          # Manchester to Split
    }

    # Add constraints for transitions between consecutive cities
    for i in range(4):
        current = order[i]
        next_city = order[i + 1]
        # (current, next_city) must be in allowed_transitions
        s.add(Or([And(current == c, next_city == n) for c, n in allowed_transitions]))

    # Now, create sum_d variables and constraints
    sum_d = [Int(f'sum_d_{i}') for i in range(5)]

    # Compute durations for each order[i]
    for i in range(5):
        # duration_i depends on order[i]
        duration_i = If(order[i] == 0, 7,
                        If(order[i] == 1, 6,
                           If(order[i] == 2, 2,
                              If(order[i] == 3, 2, 7))))
        if i == 0:
            s.add(sum_d[i] == duration_i)
        else:
            s.add(sum_d[i] == sum_d[i - 1] + duration_i)

    # Add constraints for Manchester (2) and Lyon (3)
    for i in range(5):
        # Compute start_day and end_day for this city
        if i == 0:
            start_day = 1
        else:
            start_day = sum_d[i - 1] - (i - 1)
        end_day = sum_d[i] - i

        # Manchester (2) must be on days 19-20
        manchester_cond = And(start_day == 19, end_day == 20)
        s.add(If(order[i] == 2, manchester_cond, True))

        # Lyon (3) must be on days 13-14
        lyon_cond = And(start_day == 13, end_day == 14)
        s.add(If(order[i] == 3, lyon_cond, True))

    # Ensure the total end day is 20
    s.add(sum_d[4] - 4 == 20)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()

        # Extract the order
        order_values = [model.eval(order[i]).as_long() for i in range(5)]

        # Compute sum_d values
        sum_d_values = [model.eval(sum_d[i]).as_long() for i in range(5)]

        # Now compute start and end days for each city in the order
        itinerary = []
        city_names = {0: 'Hamburg', 1: 'Munich', 2: 'Manchester', 3: 'Lyon', 4: 'Split'}
        for i in range(5):
            city_id = order_values[i]
            if i == 0:
                start_day = 1
            else:
                start_day = sum_d_values[i - 1] - (i - 1)
            end_day = sum_d_values[i] - i
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({
                "day_range": day_range,
                "place": city_names[city_id]
            })

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()