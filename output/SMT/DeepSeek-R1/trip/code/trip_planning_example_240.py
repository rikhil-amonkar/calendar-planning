from z3 import *

def main():
    s = Solver()
    cities = {'Prague': 0, 'Berlin': 1, 'Tallinn': 2, 'Stockholm': 3}
    city_names = {v: k for k, v in cities.items()}
    days_total = 12

    # Each day is assigned to a city (0-3)
    day_city = [Int(f'day_{i+1}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 3)

    # Total days in each city
    total_prague = sum([If(dc == cities['Prague'], 1, 0) for dc in day_city])
    total_berlin = sum([If(dc == cities['Berlin'], 1, 0) for dc in day_city])
    total_tallinn = sum([If(dc == cities['Tallinn'], 1, 0) for dc in day_city])
    total_stockholm = sum([If(dc == cities['Stockholm'], 1, 0) for dc in day_city])

    s.add(total_prague == 2)
    s.add(total_berlin == 3)
    s.add(total_tallinn == 5)
    s.add(total_stockholm == 5)

    # Conference in Berlin on days 6 and 8 (1-based index)
    s.add(day_city[5] == cities['Berlin'])  # Day 6
    s.add(day_city[7] == cities['Berlin'])  # Day 8

    # Tallinn days must be between day 8 and 12 (inclusive)
    for i in range(days_total):
        day_number = i + 1
        s.add(Implies(day_city[i] == cities['Tallinn'], And(day_number >= 8, day_number <= 12)))

    # Direct flights between consecutive days
    direct_flights = {
        cities['Prague']: [cities['Tallinn'], cities['Stockholm']],
        cities['Berlin']: [cities['Tallinn'], cities['Stockholm']],
        cities['Tallinn']: [cities['Prague'], cities['Berlin'], cities['Stockholm']],
        cities['Stockholm']: [cities['Prague'], cities['Berlin'], cities['Tallinn']]
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        # Either stay or take a direct flight
        s.add(Or(
            current == next_c,
            Or([And(current == c, next_c == n) for c in direct_flights for n in direct_flights[c]])
        ))

    if s.check() == sat:
        model = s.model()
        schedule = [model.evaluate(day).as_long() for day in day_city]
        print("Day  City")
        for idx, city_code in enumerate(schedule):
            print(f"{idx + 1:3}  {city_names[city_code]}")
    else:
        print("No valid trip plan exists.")

if __name__ == "__main__":
    main()