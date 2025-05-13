from z3 import *

def main():
    s = Solver()
    cities = {
        'Salzburg': 0,
        'Venice': 1,
        'Bucharest': 2,
        'Brussels': 3,
        'Hamburg': 4,
        'Copenhagen': 5,
        'Nice': 6,
        'Zurich': 7,
        'Naples': 8
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 25

    # Assign each day to a city (0-8)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 8)

    # Total days per city constraints (Salzburg:2, Venice:5, Bucharest:4, Brussels:2, Hamburg:4, Copenhagen:4, Nice:3, Zurich:5, Naples:4)
    totals = [2, 5, 4, 2, 4, 4, 3, 5, 4]
    for city_code in range(9):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Nice days (1-based 9-11 → 0-based 8-10)
    for i in range(8, 11):
        s.add(day_city[i] == cities['Nice'])
    # Fixed Copenhagen days (1-based 18-21 → 0-based 17-20)
    for i in range(17, 21):
        s.add(day_city[i] == cities['Copenhagen'])
    # Fixed Brussels days (1-based 21-22 → 0-based 20-21)
    for i in [20, 21]:
        s.add(day_city[i] == cities['Brussels'])
    # Fixed Naples days (1-based 22-25 → 0-based 21-24)
    for i in range(21, 25):
        s.add(day_city[i] == cities['Naples'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 4],          # Salzburg: self, Hamburg
        1: [1, 3, 8, 5, 7, 6, 4],  # Venice: self, Brussels, Naples, Copenhagen, Zurich, Nice, Hamburg
        2: [2, 5, 4, 3, 8, 7],     # Bucharest: self, Copenhagen, Hamburg, Brussels, Naples, Zurich
        3: [3, 7, 1, 2, 4, 6, 5, 8],  # Brussels: self, Zurich, Venice, Bucharest, Hamburg, Nice, Copenhagen, Naples
        4: [4, 6, 2, 3, 5, 1, 7, 0],  # Hamburg: self, Nice, Bucharest, Brussels, Copenhagen, Venice, Zurich, Salzburg
        5: [5, 2, 8, 3, 6, 1, 4, 7],  # Copenhagen: self, Bucharest, Naples, Brussels, Nice, Venice, Hamburg, Zurich
        6: [6, 7, 4, 3, 8, 1, 5],    # Nice: self, Zurich, Hamburg, Brussels, Naples, Venice, Copenhagen
        7: [7, 3, 6, 8, 5, 1, 4, 2],  # Zurich: self, Brussels, Nice, Naples, Copenhagen, Venice, Hamburg, Bucharest
        8: [8, 1, 2, 5, 6, 3]       # Naples: self, Venice, Bucharest, Copenhagen, Nice, Brussels
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