import z3
import json

def main():
    city_names = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    city_codes = {name: i for i, name in enumerate(city_names)}
    durations = [2, 3, 3, 4, 5, 5, 2]  # Porto, Geneva, Mykonos, Manchester, Hamburg, Naples, Frankfurt

    # Define order variables
    order = [z3.Int(f'order_{i}') for i in range(7)]
    s = z3.Solver()

    # Constraints for order variables
    for i in range(7):
        s.add(order[i] >= 0, order[i] <= 6)
    s.add(z3.Distinct(order))

    # Allowed flights
    flight_pairs = [
        ('Hamburg', 'Frankfurt'),
        ('Naples', 'Mykonos'),
        ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'),
        ('Mykonos', 'Geneva'),
        ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'),
        ('Frankfurt', 'Naples'),
        ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'),
        ('Porto', 'Manchester'),
        ('Hamburg', 'Manchester'),
    ]
    allowed_flights = set()
    for a, b in flight_pairs:
        a_code = city_codes[a]
        b_code = city_codes[b]
        allowed_flights.add((a_code, b_code))
        allowed_flights.add((b_code, a_code))

    # Flight constraints between consecutive cities
    for i in range(6):
        current = order[i]
        next_city = order[i+1]
        constraints = []
        for (x, y) in allowed_flights:
            constraints.append(z3.And(current == x, next_city == y))
        s.add(z3.Or(constraints))

    # Start and end day variables
    start_day = [z3.Int(f'start_day_{i}') for i in range(7)]
    end_day = [z3.Int(f'end_day_{i}') for i in range(7)]

    # Define duration based on city code
    def get_duration(city_code_var):
        return z3.If(city_code_var == 0, 2,
                     z3.If(city_code_var == 1, 3,
                           z3.If(city_code_var == 2, 3,
                                 z3.If(city_code_var == 3, 4,
                                       z3.If(city_code_var == 4, 5,
                                             z3.If(city_code_var == 5, 5, 2)))))))

    # Constraints for start and end days
    s.add(start_day[0] == 1)
    s.add(end_day[0] == start_day[0] + get_duration(order[0]) - 1)

    for i in range(1, 7):
        s.add(start_day[i] == end_day[i-1])
        s.add(end_day[i] == start_day[i] + get_duration(order[i]) - 1)

    s.add(end_day[6] == 18)

    # Specific time constraints
    for i in range(7):
        # Mykonos (code 2) must be between day 10-12
        s.add(z3.Implies(order[i] == 2, z3.And(start_day[i] >= 8, start_day[i] <= 12)))
        # Manchester (code 3) must be during days 15-18
        s.add(z3.Implies(order[i] == 3, z3.And(start_day[i] >= 12, start_day[i] <= 15)))
        # Frankfurt (code 6) must start on day 5
        s.add(z3.Implies(order[i] == 6, start_day[i] == 5))

    # Check if satisfiable
    if s.check() == z3.sat:
        model = s.model()
        order_values = [model.evaluate(order[i]).as_long() for i in range(7)]
        start_days = [model.evaluate(start_day[i]).as_long() for i in range(7)]
        end_days = [model.evaluate(end_day[i]).as_long() for i in range(7)]

        # Build the itinerary
        itinerary = []
        for i in range(7):
            city_name = city_names[order_values[i]]
            start = start_days[i]
            end = end_days[i]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()