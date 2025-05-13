from z3 import *

def main():
    s = Solver()
    cities = {
        'Porto': 0,
        'Prague': 1,
        'Reykjavik': 2,
        'Santorini': 3,
        'Amsterdam': 4,
        'Munich': 5
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 16

    # Each day is assigned to a city (0-5)
    day_city = [Int(f'day_{i+1}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 5)

    # Total days per city
    totals = [0]*6
    totals[cities['Porto']] = 5
    totals[cities['Prague']] = 4
    totals[cities['Reykjavik']] = 4
    totals[cities['Santorini']] = 2
    totals[cities['Amsterdam']] = 2
    totals[cities['Munich']] = 4

    for city_code in range(6):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Amsterdam on days 14 and 15 (0-based index 13 and 14)
    s.add(day_city[13] == cities['Amsterdam'])
    s.add(day_city[14] == cities['Amsterdam'])

    # Reykjavik days must be between day 4 and 7 (inclusive)
    for i in range(days_total):
        day_number = i + 1
        s.add(Implies(day_city[i] == cities['Reykjavik'], And(day_number >= 4, day_number <= 7)))

    # At least one Munich day between day7 and day10
    munich_in_window = []
    for i in range(6, 10):  # days 7-10 (indices 6-9)
        munich_in_window.append(day_city[i] == cities['Munich'])
    s.add(Or(munich_in_window))

    # Direct flights between consecutive days
    direct_flights = {
        cities['Porto']: [cities['Amsterdam'], cities['Munich']],
        cities['Prague']: [cities['Reykjavik'], cities['Amsterdam'], cities['Munich']],
        cities['Reykjavik']: [cities['Prague'], cities['Amsterdam'], cities['Munich']],
        cities['Santorini']: [cities['Amsterdam']],
        cities['Amsterdam']: [cities['Porto'], cities['Munich'], cities['Reykjavik'], cities['Prague'], cities['Santorini']],
        cities['Munich']: [cities['Porto'], cities['Amsterdam'], cities['Reykjavik'], cities['Prague']]
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        s.add(Or(
            current == next_c,
            Or([And(current == c, next_c in direct_flights[c]) for c in direct_flights])
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