from z3 import *

def solve_itinerary():
    s = Solver()

    days = list(range(1, 13))  # Days 1 to 12
    cities = ['Dublin', 'Riga', 'Vilnius']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    flights = {
        'Dublin': ['Riga'],
        'Riga': ['Dublin', 'Vilnius'],
        'Vilnius': ['Riga']
    }

    required_days = {
        'Dublin': 2,
        'Riga': 5,
        'Vilnius': 7
    }

    # Variable for each day: which city are we in?
    day_city = [Int(f'day_{day}_city') for day in days]
    for dc in day_city:
        s.add(Or([dc == city_to_idx[city] for city in cities]))

    # Constraint: total days in each city must match required_days
    for city in cities:
        s.add(Sum([If(day_city[day - 1] == city_to_idx[city], 1, 0) for day in days) == required_days[city])

    # Constraint: consecutive days must be same city or connected by flight
    for day in range(1, 12):
        current = day_city[day - 1]
        next_ = day_city[day]
        s.add(Or(
            current == next_,
            And(
                current != next_,
                Or(
                    [And(
                        current == city_to_idx[depart],
                        next_ == city_to_idx[arrive]
                    ) for depart in flights for arrive in flights[depart]]
                )
            )
        ))

    # Ensure the first day is in one of the cities
    s.add(Or([day_city[0] == city_to_idx[city] for city in cities]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1

        for day in days:
            city_idx = model.evaluate(day_city[day - 1]).as_long()
            city = cities[city_idx]
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day

        if start_day == days[-1]:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days[-1]}", "place": current_city})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(itinerary)