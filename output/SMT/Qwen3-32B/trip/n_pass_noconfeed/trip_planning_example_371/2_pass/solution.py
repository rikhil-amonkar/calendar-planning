import z3
import json

def main():
    solver = z3.Solver()

    # Define cities as integers
    VIENNA = 0
    NICE = 1
    STOCKHOLM = 2
    SPLIT = 3

    allowed_flights = [
        (VIENNA, STOCKHOLM), (STOCKHOLM, VIENNA),
        (VIENNA, NICE), (NICE, VIENNA),
        (VIENNA, SPLIT), (SPLIT, VIENNA),
        (STOCKHOLM, SPLIT), (SPLIT, STOCKHOLM),
        (NICE, STOCKHOLM), (STOCKHOLM, NICE)
    ]

    # Create variables for current_city for each day 1-9 (0-based index 0-8)
    current_city = [z3.Int(f'current_city_{d}') for d in range(9)]

    # Create variables for flight (whether there is a flight on day d, for d 1-8 (0-based index 0-7))
    flight = [z3.Bool(f'flight_{d}') for d in range(8)]

    # Create variables for next_city for each day d 1-8 (0-based index 0-7)
    next_city = [z3.Int(f'next_city_{d}') for d in range(8)]

    # Add constraints for transitions between days
    for d in range(8):
        current_city_d = current_city[d]
        next_city_d = next_city[d]
        current_city_next_day = current_city[d + 1]
        solver.add(current_city_next_day == z3.If(flight[d], next_city_d, current_city_d))

        allowed_pairs = []
        for a, b in allowed_flights:
            allowed_pairs.append(z3.And(current_city_d == a, next_city_d == b))
        solver.add(z3.Implies(flight[d], z3.Or(allowed_pairs)))

    # Function to compute duration constraints
    def get_duration_constraints(city, required_days):
        sum_current = 0
        for d in range(9):
            sum_current += z3.If(current_city[d] == city, 1, 0)
        return sum_current == required_days

    # Add duration constraints
    solver.add(get_duration_constraints(VIENNA, 2))
    solver.add(get_duration_constraints(NICE, 2))
    solver.add(get_duration_constraints(STOCKHOLM, 3))
    solver.add(get_duration_constraints(SPLIT, 2))

    # Conference on day 7 and 9 (0-based index 6 and 8)
    solver.add(current_city[6] == SPLIT)
    solver.add(current_city[8] == SPLIT)

    # Workshop in Vienna between day 1 and day 2
    solver.add(z3.Or(current_city[0] == VIENNA, current_city[1] == VIENNA))

    # Solve
    if solver.check() == z3.sat:
        model = solver.model()

        # Extract current_city values
        days = []
        for d in range(9):
            city_val = model.eval(current_city[d]).as_long()
            days.append(city_val)

        # Group consecutive days into ranges
        itinerary = []
        current_place = days[0]
        start_day = 1
        for i in range(1, 9):
            if days[i] != current_place:
                end_day = i
                city_name = {VIENNA: 'Vienna', NICE: 'Nice', STOCKHOLM: 'Stockholm', SPLIT: 'Split'}[current_place]
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': city_name
                })
                current_place = days[i]
                start_day = i + 1
        # Add the last segment
        end_day = 9
        city_name = {VIENNA: 'Vienna', NICE: 'Nice', STOCKHOLM: 'Stockholm', SPLIT: 'Split'}[current_place]
        itinerary.append({
            'day_range': f"Day {start_day}-{end_day}",
            'place': city_name
        })

        # Output JSON
        print(json.dumps({'itinerary': itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()