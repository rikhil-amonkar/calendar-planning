import z3

def main():
    cities = ["Brussels", "Venice", "Santorini", "Lisbon", "Reykjavik", "London", "Madrid"]
    c2i = {c: i for i, c in enumerate(cities)}
    
    # Flight connections as tuples (from, to)
    flights = set()
    # Add bidirectional flights
    for (a, b) in [
        ("Venice", "Madrid"), ("Lisbon", "Reykjavik"), ("Brussels", "Venice"),
        ("Venice", "Santorini"), ("Lisbon", "Venice"), ("Brussels", "London"),
        ("Madrid", "London"), ("Santorini", "London"), ("London", "Reykjavik"),
        ("Brussels", "Lisbon"), ("Lisbon", "London"), ("Lisbon", "Madrid"),
        ("Madrid", "Santorini"), ("Brussels", "Reykjavik"), ("Brussels", "Madrid"),
        ("Venice", "London")
    ]:
        flights.add((c2i[a], c2i[b]))
        flights.add((c2i[b], c2i[a]))
    # Add unidirectional flight
    flights.add((c2i["Reykjavik"], c2i["Madrid"]))
    
    # Required days per city
    days_req = {
        c2i["Brussels"]: 2,
        c2i["Venice"]: 3,
        c2i["Santorini"]: 3,
        c2i["Lisbon"]: 4,
        c2i["Reykjavik"]: 3,
        c2i["London"]: 3,
        c2i["Madrid"]: 5
    }
    
    s = z3.Solver()
    # City at end of each day (17 days)
    c = [z3.Int(f"d{i}") for i in range(17)]
    
    # All cities must be valid integers (0-6)
    for city_var in c:
        s.add(z3.And(city_var >= 0, city_var < 7))
    
    # Start and end in Brussels for conference (days 1-2)
    s.add(c[0] == c2i["Brussels"])
    s.add(c[1] == c2i["Brussels"])
    
    # Wedding in Madrid (days 7-11)
    for day in range(6, 11):  # Days 6-10 (0-indexed) = days 7-11
        s.add(z3.Or(c[day] == c2i["Madrid"], c[day-1] == c2i["Madrid"]))
    
    # Visit Venice between days 5-7
    s.add(z3.Or(
        c[3] == c2i["Venice"],  # Day 5 start
        c[4] == c2i["Venice"],  # Day 5 end / Day 6 start
        c[5] == c2i["Venice"],  # Day 6 end / Day 7 start
        c[6] == c2i["Venice"]   # Day 7 end
    ))
    
    # Flight transitions
    for i in range(17):
        start_city = c2i["Brussels"] if i == 0 else c[i-1]
        end_city = c[i]
        # Either stay in same city or use valid flight
        s.add(z3.Or(
            start_city == end_city,
            z3.Or([z3.And(start_city == f[0], end_city == f[1]) for f in flights])
        ))
    
    # Count days per city
    for city_idx, req_days in days_req.items():
        count = 0
        for i in range(17):
            start = c2i["Brussels"] if i == 0 else c[i-1]
            end = c[i]
            # Count if city appears at start or end of day
            count += z3.If(z3.Or(start == city_idx, end == city_idx), 1, 0)
        s.add(count == req_days)
    
    # Solve and output
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for i in range(17):
            city_idx = m.evaluate(c[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()