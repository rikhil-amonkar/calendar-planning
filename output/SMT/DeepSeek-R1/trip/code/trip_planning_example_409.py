from z3 import *

def main():
    s = Solver()
    cities = {
        'Hamburg': 0,
        'Zurich': 1,
        'Helsinki': 2,
        'Bucharest': 3,
        'Split': 4
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 12

    # Each day is assigned to a city (0-4)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 4)

    # Total days per city
    totals = [2, 3, 2, 2, 7]  # Hamburg, Zurich, Helsinki, Bucharest, Split

    for city_code in range(5):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Zurich must be on days 1-3 (indices 0,1,2)
    s.add(day_city[0] == cities['Zurich'])
    s.add(day_city[1] == cities['Zurich'])
    s.add(day_city[2] == cities['Zurich'])

    # Split must be on days 4 and 10 (indices 3 and 9)
    s.add(day_city[3] == cities['Split'])
    s.add(day_city[9] == cities['Split'])

    # Direct flights between consecutive days
    direct_flights = {
        cities['Hamburg']: [cities['Bucharest'], cities['Zurich'], cities['Helsinki'], cities['Split']],
        cities['Zurich']: [cities['Helsinki'], cities['Hamburg'], cities['Bucharest'], cities['Split']],
        cities['Helsinki']: [cities['Zurich'], cities['Hamburg'], cities['Split']],
        cities['Bucharest']: [cities['Hamburg'], cities['Zurich']],
        cities['Split']: [cities['Zurich'], cities['Helsinki'], cities['Hamburg']]
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        allowed = [current == next_c]
        allowed += [next_c == n for n in direct_flights.get(current, [])]
        s.add(Or(allowed))

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