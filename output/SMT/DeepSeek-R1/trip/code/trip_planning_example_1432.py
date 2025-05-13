from z3 import *

def main():
    s = Solver()
    cities = {
        'Frankfurt': 0,
        'Salzburg': 1,
        'Athens': 2,
        'Reykjavik': 3,
        'Bucharest': 4,
        'Valencia': 5,
        'Vienna': 6,
        'Amsterdam': 7,
        'Stockholm': 8,
        'Riga': 9
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 29

    # Assign each day to a city (0-9)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 9)

    # Total days per city constraints
    totals = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
    for city_code in range(10):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based days)
    # Valencia days 4-5 (1-based 5-6)
    s.add(day_city[4] == cities['Valencia'])
    s.add(day_city[5] == cities['Valencia'])
    # Vienna days 5-9 (1-based 6-10)
    for i in range(5, 10):
        s.add(day_city[i] == cities['Vienna'])
    # Stockholm days 0-2 (1-based 1-3)
    for i in range(3):
        s.add(day_city[i] == cities['Stockholm'])
    # Athens days 13-17 (1-based 14-18)
    for i in range(13, 18):
        s.add(day_city[i] == cities['Athens'])
    # Riga days 17-19 (1-based 18-20)
    for i in range(17, 20):
        s.add(day_city[i] == cities['Riga'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0,5,9,7,1,4,8,2,3],   # Frankfurt
        1: [1,0],                  # Salzburg
        2: [2,4,8,9,7,0,6],       # Athens
        3: [3,0,7,8,2,6],         # Reykjavik
        4: [4,6,2,7,5,0,9],       # Bucharest
        5: [5,0,2,4,6,7],         # Valencia
        6: [6,4,8,9,0,5,7,3,2],  # Vienna
        7: [7,4,0,3,8,5,9,6,2],  # Amsterdam
        8: [8,2,6,7,3,0,9],      # Stockholm
        9: [9,0,6,7,8,4]         # Riga
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