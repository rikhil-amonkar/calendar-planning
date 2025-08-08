import z3

def main():
    cities = ["Prague", "Lyon", "Frankfurt", "Helsinki", "Naples"]
    city_to_num = {c: idx for idx, c in enumerate(cities)}
    num_to_city = {idx: c for idx, c in enumerate(cities)}
    
    direct_pairs = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    direct_flights_set = set()
    for a, b in direct_pairs:
        i = city_to_num[a]
        j = city_to_num[b]
        direct_flights_set.add((i, j))
        direct_flights_set.add((j, i))
    
    required_days = {
        "Prague": 2,
        "Lyon": 3,
        "Frankfurt": 3,
        "Helsinki": 4,
        "Naples": 4
    }
    req_days_list = [required_days[c] for c in cities]
    
    s = z3.Solver()
    stay = [z3.Int(f"stay_{i}") for i in range(1, 13)]
    for i in range(12):
        s.add(stay[i] >= 0, stay[i] < 5)
    
    fly = [z3.Bool(f"fly_{i}") for i in range(1, 12)]
    
    for i in range(11):
        flight_options = []
        for (a, b) in direct_flights_set:
            flight_options.append(z3.And(stay[i] == a, stay[i+1] == b))
        s.add(z3.Implies(fly[i], z3.Or(flight_options)))
    
    for d in [1, 2, 3, 4]:
        s.add(z3.Or(
            stay[d] == city_to_num["Helsinki"],
            z3.And(fly[d], stay[d+1] == city_to_num["Helsinki"])
        ))
    
    in_prague_day1 = z3.Or(
        stay[0] == city_to_num["Prague"],
        z3.And(fly[0], stay[1] == city_to_num["Prague"])
    )
    in_prague_day2 = z3.Or(
        stay[1] == city_to_num["Prague"],
        z3.And(fly[1], stay[2] == city_to_num["Prague"])
    )
    s.add(z3.Or(in_prague_day1, in_prague_day2))
    
    total_days_per_city = [0] * 5
    for c in range(5):
        total = 0
        for d in range(12):
            if d < 11:
                in_city = z3.If(fly[d],
                                z3.Or(stay[d] == c, stay[d+1] == c),
                                stay[d] == c)
            else:
                in_city = (stay[d] == c)
            total += z3.If(in_city, 1, 0)
        s.add(total == req_days_list[c])
    
    flight_count = z3.Sum([z3.If(fly[i], 1, 0) for i in range(11)])
    s.add(flight_count == 4)
    
    if s.check() == z3.sat:
        model = s.model()
        itinerary = []
        for d in range(12):
            if d < 11 and z3.is_true(model.eval(fly[d])):
                city1_idx = model.eval(stay[d]).as_long()
                city2_idx = model.eval(stay[d+1]).as_long()
                places = [num_to_city[city1_idx], num_to_city[city2_idx]]
            else:
                city_idx = model.eval(stay[d]).as_long()
                places = [num_to_city[city_idx]]
            itinerary.append({"day": d+1, "place": places})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()