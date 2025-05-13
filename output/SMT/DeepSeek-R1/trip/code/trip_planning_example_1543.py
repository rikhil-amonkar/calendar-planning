from z3 import *

def main():
    s = Solver()
    cities = {
        'Prague': 0,
        'Warsaw': 1,
        'Dublin': 2,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 6,
        'Seville': 7,
        'Lisbon': 8,
        'Dubrovnik': 9
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 26

    # Each day is assigned to a city (0-9)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 9)

    # Total days per city
    totals = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]  # Order matches cities dict

    for city_code in range(10):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Prague days 1-3 (0-based 0,1,2)
    s.add(day_city[0] == cities['Prague'])
    s.add(day_city[1] == cities['Prague'])
    s.add(day_city[2] == cities['Prague'])

    # London days 3-5 (0-based 2,3,4)
    s.add(day_city[2] == cities['London'])  # Conflict with Prague
    s.add(day_city[3] == cities['London'])
    s.add(day_city[4] == cities['London'])

    # Lisbon days 5-9 (0-based 4-8)
    for i in range(4, 9):
        s.add(day_city[i] == cities['Lisbon'])

    # Porto days 16-20 (0-based 15-19)
    for i in range(15, 20):
        s.add(day_city[i] == cities['Porto'])

    # Warsaw days 20-23 (0-based 19-22)
    for i in range(19, 23):
        s.add(day_city[i] == cities['Warsaw'])

    # Direct flights between consecutive days
    direct_flights = {
        cities['Prague']: [3, 8, 6, 1, 2, 0],
        cities['Warsaw']: [4, 6, 8, 5, 0, 3, 1],
        cities['Dublin']: [6, 3, 7, 5, 0, 8, 9, 2],
        cities['Athens']: [0, 4, 2, 1, 5, 8, 9, 3],
        cities['Vilnius']: [1, 3, 4],
        cities['Porto']: [8, 7, 2, 1, 3, 5],
        cities['London']: [8, 2, 0, 1, 3, 6],
        cities['Seville']: [2, 5, 8, 7],
        cities['Lisbon']: [6, 5, 0, 3, 1, 2, 7, 8],
        cities['Dubrovnik']: [3, 2, 9]
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        allowed = [next_c == n for n in direct_flights.get(current, [current])]
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