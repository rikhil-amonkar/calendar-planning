from z3 import *
import json

def solve_itinerary():
    # Define city mappings
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}

    # Allowed direct flights (bidirectional)
    allowed_flights = [
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split')
    ]
    allowed_pairs = set()
    for a, b in allowed_flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))

    # Create Z3 solver
    s = Solver()

    # Day assignments: day_to_city[i] represents the city on day i+1 (1-based days)
    day_to_city = [Int(f'day_{i}') for i in range(1, 17)]
    for day in day_to_city:
        s.add(day >= 0, day < len(cities))

    # Flight constraints between consecutive days
    for i in range(15):
        current_city = day_to_city[i]
        next_city = day_to_city[i+1]
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city,
                Or(*[And(current_city == city_to_num[a], next_city == city_to_num[b])
                    for a, b in allowed_pairs]))
        ))

    # Duration constraints
    for city, days in [('Dubrovnik', 4), ('Split', 3), ('Milan', 3), ('Porto', 4), ('Krakow', 2), ('Munich', 5)]:
        s.add(Sum([If(day_to_city[i] == city_to_num[city], 1, 0) for i in range(16)]) == days)

    # Event constraints
    # Munich show from day 4 to 8 (days 4,5,6,7,8)
    for i in range(3, 8):  # 0-based days 3 to 7 (1-based 4 to 8)
        s.add(day_to_city[i] == city_to_num['Munich'])

    # Wedding in Milan between day 11-13 (days 11,12,13)
    for i in range(10, 13):  # 0-based days 10 to 12 (1-based 11 to 13)
        s.add(day_to_city[i] == city_to_num['Milan'])

    # Meet friends in Krakow between day 8-9 (days 8 or 9)
    s.add(Or(
        day_to_city[7] == city_to_num['Krakow'],  # day 8
        day_to_city[8] == city_to_num['Krakow']   # day 9
    ))

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary_days = []
        for i in range(16):
            day_num = i + 1
            city_num = model.evaluate(day_to_city[i]).as_long()
            itinerary_days.append((day_num, num_to_city[city_num]))

        # Build the itinerary with day ranges and flight days
        itinerary = []
        current_place = itinerary_days[0][1]
        start_day = 1

        for i in range(1, 16):
            day_num, place = itinerary_days[i]
            if place != current_place:
                # Add the stay up to the previous day
                if start_day == day_num - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day_num - 1}", "place": current_place})
                # Add the flight day (day_num is the transition day)
                itinerary.append({"day_range": f"Day {day_num}", "place": current_place})
                itinerary.append({"day_range": f"Day {day_num}", "place": place})
                current_place = place
                start_day = day_num
        # Add the last stay
        if start_day <= 16:
            if start_day == 16:
                itinerary.append({"day_range": f"Day {16}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-16", "place": current_place})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))