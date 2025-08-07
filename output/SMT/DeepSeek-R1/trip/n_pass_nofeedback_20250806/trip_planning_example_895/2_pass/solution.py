import z3

def main():
    cities = ["Brussels", "Venice", "Santorini", "Lisbon", "Reykjavik", "London", "Madrid"]
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    total_days_dict = {
        "Brussels": 2,
        "Venice": 3,
        "Santorini": 3,
        "Lisbon": 4,
        "Reykjavik": 3,
        "London": 3,
        "Madrid": 5
    }
    
    directed_flights = []
    bidirectional = [
        ("Venice", "Madrid"),
        ("Lisbon", "Reykjavik"),
        ("Brussels", "Venice"),
        ("Venice", "Santorini"),
        ("Lisbon", "Venice"),
        ("Brussels", "London"),
        ("Madrid", "London"),
        ("Santorini", "London"),
        ("London", "Reykjavik"),
        ("Brussels", "Lisbon"),
        ("Lisbon", "London"),
        ("Lisbon", "Madrid"),
        ("Madrid", "Santorini"),
        ("Brussels", "Reykjavik"),
        ("Brussels", "Madrid"),
        ("Venice", "London")
    ]
    for a, b in bidirectional:
        a_int = city_to_int[a]
        b_int = city_to_int[b]
        directed_flights.append((a_int, b_int))
        directed_flights.append((b_int, a_int))
    directed_flights.append((city_to_int["Reykjavik"], city_to_int["Madrid"]))
    
    s = z3.Solver()
    c = [z3.Int(f"c_{i}") for i in range(17)]
    
    brussels = city_to_int["Brussels"]
    venice = city_to_int["Venice"]
    madrid = city_to_int["Madrid"]
    
    s.add(c[0] == brussels)
    s.add(c[1] == brussels)
    
    for day in range(7, 12):
        idx = day - 1
        start_city = c[idx - 1] if idx > 0 else brussels
        end_city = c[idx]
        s.add(z3.Or(start_city == madrid, end_city == madrid))
    
    venice_days = []
    for day in [5, 6, 7]:
        idx = day - 1
        start_city = c[idx - 1] if idx > 0 else brussels
        end_city = c[idx]
        venice_days.append(z3.Or(start_city == venice, end_city == venice))
    s.add(z3.Or(venice_days))
    
    for city, total_days in total_days_dict.items():
        city_int = city_to_int[city]
        days = []
        for i in range(17):
            if i == 0:
                start = brussels
            else:
                start = c[i-1]
            end = c[i]
            days.append(z3.If(z3.Or(start == city_int, end == city_int), 1, 0))
        s.add(z3.Sum(days) == total_days)
    
    for i in range(17):
        if i == 0:
            start_city = brussels
        else:
            start_city = c[i-1]
        end_city = c[i]
        s.add(z3.And(end_city >= 0, end_city < len(cities)))
        same_city = start_city == end_city
        flight_exists = z3.Or([z3.And(start_city == a, end_city == b) for a, b in directed_flights])
        s.add(z3.Or(same_city, flight_exists))
    
    if s.check() == z3.sat:
        model = s.model()
        itinerary = []
        for i in range(17):
            city_int = model.evaluate(c[i]).as_long()
            itinerary.append({"day": i+1, "place": int_to_city[city_int]})
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()