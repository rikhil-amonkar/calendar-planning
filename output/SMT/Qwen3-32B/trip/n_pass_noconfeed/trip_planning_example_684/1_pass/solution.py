from z3 import *
import json

def main():
    # Define cities and durations
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    durations = [4, 5, 5, 5, 4, 5]  # 0:Amsterdam, 1:Edinburgh, 2:Brussels, 3:Vienna, 4:Berlin, 5:Reykjavik
    allowed_transitions = {
        (0,4), (4,0),
        (1,4), (4,1),
        (1,0), (0,1),
        (3,4), (4,3),
        (4,2), (2,4),
        (3,5), (5,3),
        (1,2), (2,1),
        (3,2), (2,3),
        (0,5), (5,0),
        (5,2), (2,5),
        (0,3), (3,0),
        (5,4), (4,5),
    }

    # Solver
    s = Solver()

    # Order variables
    order = [Int(f'order_{i}') for i in range(6)]
    for city in order:
        s.add(And(0 <= city, city <= 5))
    s.add(Distinct(order))

    # Allowed transitions between consecutive cities
    for i in range(5):
        a, b = order[i], order[i+1]
        transitions_expr = Or([And(a == from_city, b == to_city) for from_city, to_city in allowed_transitions])
        s.add(transitions_expr)

    # Define get_duration function for a city variable
    def get_duration(city_var):
        return If(Or(city_var == 0, city_var == 4), 4, 5)

    # Define sum variables for cumulative durations
    sum_0 = 0
    sum_1 = sum_0 + (get_duration(order[0]) - 1)
    sum_2 = sum_1 + (get_duration(order[1]) - 1)
    sum_3 = sum_2 + (get_duration(order[2]) - 1)
    sum_4 = sum_3 + (get_duration(order[3]) - 1)
    sum_5 = sum_4 + (get_duration(order[4]) - 1)

    # Create start and end variables for each city
    start = [Int(f'start_{i}') for i in range(6)]
    end = [Int(f'end_{i}') for i in range(6)]

    for city_id in range(6):
        for i in range(6):
            # If order[i] == city_id, then start[city_id] = 1 + sum_i
            # and end[city_id] = sum_i + duration
            duration_expr = If(Or(city_id == 0, city_id == 4), 4, 5)
            sum_i = [sum_0, sum_1, sum_2, sum_3, sum_4, sum_5][i]
            s.add(Implies(order[i] == city_id, start[city_id] == 1 + sum_i))
            s.add(Implies(order[i] == city_id, end[city_id] == sum_i + duration_expr))

    # Add time window constraints
    # Amsterdam (0): visit relatives between day 5 and 8
    s.add(And(start[0] <= 8, end[0] >= 5))
    # Reykjavik (5): workshop between day 12 and 16
    s.add(And(start[5] <= 16, end[5] >= 12))
    # Berlin (4): meet friend between day 16 and 19
    s.add(And(start[4] <= 19, end[4] >= 16))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract order
        order_values = [model[order[i]].as_long() for i in range(6)]
        # Extract start and end for each city
        start_values = [model[start[i]].as_long() for i in range(6)]
        end_values = [model[end[i]].as_long() for i in range(6)]

        # Now build the itinerary
        itinerary = []
        for i in range(6):
            city_id = order_values[i]
            city_name = cities[city_id]
            start_day = start_values[city_id]
            end_day = end_values[city_id]
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()