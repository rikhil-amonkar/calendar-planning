from z3 import *

def main():
    s = Solver()
    cities = {
        'Oslo': 0,
        'Helsinki': 1,
        'Edinburgh': 2,
        'Riga': 3,
        'Tallinn': 4,
        'Budapest': 5,
        'Vilnius': 6,
        'Porto': 7,
        'Geneva': 8
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 25

    # Assign each day to a city (0-8)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 8)

    # Total days per city constraints
    totals = [2, 2, 3, 2, 5, 5, 5, 5, 4]
    for city_code in range(9):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Oslo days 23-24 (1-based 24-25)
    s.add(day_city[23] == cities['Oslo'])
    s.add(day_city[24] == cities['Oslo'])
    # Tallinn days 3-7 (1-based 4-8)
    for i in range(3, 8):
        s.add(day_city[i] == cities['Tallinn'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0,7,3,8,2,6,5,4,1],   # Oslo
        1: [1,6,3,2,5,0,8,4],     # Helsinki
        2: [2,5,8,7,0,1,3],       # Edinburgh
        3: [3,4,0,1,2,6],         # Riga
        4: [4,0,6,1],             # Tallinn
        5: [5,2,8,1,0],           # Budapest
        6: [6,1,0],               # Vilnius
        7: [7,0,2,8],             # Porto
        8: [8,2,5,0,1,7]          # Geneva
    }

    # Ensure consecutive days are connected by direct flights
    for i in range(days_total - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_day == nc for nc in allowed]))

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