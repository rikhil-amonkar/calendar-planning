from z3 import *

def main():
    s = Solver()
    cities = {
        'Mykonos': 0,
        'Nice': 1,
        'London': 2,
        'Copenhagen': 3,
        'Oslo': 4,
        'Tallinn': 5
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 16

    # Assign each day to a city (0-5)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 5)

    # Total days per city constraints
    totals = [4, 3, 2, 3, 5, 4]
    for city_code in range(6):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Nice days 13-15 (1-based days 14-16)
    for i in range(13, 16):
        s.add(day_city[i] == cities['Nice'])
    # Oslo days 9-13 (1-based days 10-14)
    for i in range(9, 14):
        s.add(day_city[i] == cities['Oslo'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 2, 1],       # Mykonos: Mykonos, London, Nice
        1: [1, 4, 2, 0, 3], # Nice: Nice, Oslo, London, Mykonos, Copenhagen
        2: [2, 3, 1, 4, 0], # London: London, Copenhagen, Nice, Oslo, Mykonos
        3: [3, 2, 5, 1, 4], # Copenhagen: Copenhagen, London, Tallinn, Nice, Oslo
        4: [4, 5, 1, 2, 3], # Oslo: Oslo, Tallinn, Nice, London, Copenhagen
        5: [5, 3, 4]        # Tallinn: Tallinn, Copenhagen, Oslo
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