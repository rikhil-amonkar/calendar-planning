from z3 import *

def main():
    s = Solver()
    cities = {
        'Dublin': 0,
        'Helsinki': 1,
        'Riga': 2,
        'Reykjavik': 3,
        'Vienna': 4,
        'Tallinn': 5
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 15

    # Assign each day to a city (0-5)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 5)

    # Total days per city constraints
    totals = [5, 3, 3, 2, 2, 5]
    for city_code in range(6):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Helsinki days 2-4 (1-based 3-5)
    for i in [2, 3, 4]:
        s.add(day_city[i] == cities['Helsinki'])
    # Vienna days 1-2 (1-based 2-3)
    for i in [1, 2]:
        s.add(day_city[i] == cities['Vienna'])
    # Tallinn days 6-10 (1-based 7-11)
    for i in range(6, 11):
        s.add(day_city[i] == cities['Tallinn'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 1, 2, 3, 4, 5],  # Dublin
        1: [1, 2, 4, 0, 3, 5],   # Helsinki
        2: [2, 1, 0, 4, 5],      # Riga
        3: [3, 4, 1, 0],         # Reykjavik
        4: [4, 1, 2, 3, 0],     # Vienna
        5: [5, 0, 1]            # Tallinn
    }

    # Ensure consecutive days are connected by direct flights
    for i in range(days_total - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_day == a for a in allowed]))

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