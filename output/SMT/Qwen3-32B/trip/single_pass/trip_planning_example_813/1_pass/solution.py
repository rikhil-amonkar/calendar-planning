import z3
import json

def main():
    cities = ['Frankfurt', 'Dublin', 'London', 'Vilnius', 'Santorini', 'Stuttgart', 'Seville']
    durations = {
        'Frankfurt': 5,
        'Dublin': 3,
        'London': 2,
        'Vilnius': 3,
        'Santorini': 2,
        'Stuttgart': 3,
        'Seville': 5
    }

    allowed_transitions = {
        ('Frankfurt', 'Dublin'), ('Dublin', 'Frankfurt'),
        ('Frankfurt', 'London'), ('London', 'Frankfurt'),
        ('London', 'Dublin'), ('Dublin', 'London'),
        ('Vilnius', 'Frankfurt'), ('Frankfurt', 'Vilnius'),
        ('Frankfurt', 'Stuttgart'), ('Stuttgart', 'Frankfurt'),
        ('Dublin', 'Seville'), ('Seville', 'Dublin'),
        ('London', 'Santorini'), ('Santorini', 'London'),
        ('Stuttgart', 'London'), ('London', 'Stuttgart'),
        ('Santorini', 'Dublin'), ('Dublin', 'Santorini'),
    }

    s = z3.Solver()

    city_vars = [z3.String(f'city_{i}') for i in range(7)]
    for var in city_vars:
        s.add(z3.Or([var == city for city in cities]))

    s.add(z3.Distinct(city_vars))

    for i in range(6):
        current = city_vars[i]
        next_city = city_vars[i+1]
        constraints = []
        for a, b in allowed_transitions:
            constraints.append(z3.And(current == a, next_city == b))
        s.add(z3.Or(*constraints))

    start_days = [z3.Int(f'start_days_{i}') for i in range(7)]
    s.add(start_days[0] == 1)

    def get_duration_z3(city_var):
        return z3.If(city_var == 'Frankfurt', 5,
                     z3.If(city_var == 'Dublin', 3,
                           z3.If(city_var == 'London', 2,
                                 z3.If(city_var == 'Vilnius', 3,
                                       z3.If(city_var == 'Santorini', 2,
                                             z3.If(city_var == 'Stuttgart', 3,
                                                   z3.If(city_var == 'Seville', 5, 0))))))

    for i in range(1, 7):
        prev_city = city_vars[i-1]
        duration_prev = get_duration_z3(prev_city)
        s.add(start_days[i] == start_days[i-1] + duration_prev - 1)

    start_London = z3.Int('start_London')
    start_Stuttgart = z3.Int('start_Stuttgart')

    for i in range(7):
        s.add(z3.Implies(city_vars[i] == 'London', start_London == start_days[i]))
        s.add(z3.Implies(city_vars[i] == 'Stuttgart', start_Stuttgart == start_days[i]))

    s.add(z3.And(start_London >= 8, start_London <= 9))
    s.add(z3.And(start_Stuttgart >= 5, start_Stuttgart <= 9))

    if s.check() == z3.sat:
        model = s.model()
        city_order = [model.eval(city_vars[i]).as_string() for i in range(7)]
        start_days_values = [model.eval(start_days[i]).as_long() for i in range(7)]
        itinerary = []
        for i in range(7):
            city = city_order[i]
            duration = durations[city]
            start = start_days_values[i]
            end = start + duration - 1
            for day in range(start, end + 1):
                itinerary.append({'day': day, 'city': city})
        itinerary.sort(key=lambda x: x['day'])
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()