from z3 import *
import json

def main():
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    n = len(cities)
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    allowed_flights = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon")
    ]
    allowed_directed = []
    for a, b in allowed_flights:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        allowed_directed.append((a_idx, b_idx))
        allowed_directed.append((b_idx, a_idx))
    
    s = Solver()
    x = [Int('x_%d' % i) for i in range(20)]
    
    for i in range(20):
        s.add(x[i] >= 0, x[i] < n)
    
    for i in range(19):
        current = x[i]
        next_ = x[i+1]
        same_city = (current == next_)
        flight_ok = Or([And(current == a, next_ == b) for (a, b) in allowed_directed])
        s.add(Or(same_city, flight_ok))
    
    def days_in_city(c):
        total = If(x[0] == c, 1, 0)
        for i in range(1, 20):
            cond = Or(x[i] == c, And(x[i-1] == c, x[i] != c))
            total = total + If(cond, 1, 0)
        return total
    
    s.add(days_in_city(city_to_index["Nice"]) == 5)
    s.add(days_in_city(city_to_index["Krakow"]) == 6)
    s.add(days_in_city(city_to_index["Dublin"]) == 7)
    s.add(days_in_city(city_to_index["Lyon"]) == 4)
    s.add(days_in_city(city_to_index["Frankfurt"]) == 2)
    
    nice_in_period = []
    for i in range(5):
        if i == 0:
            nice_in_period.append(x[0] == city_to_index["Nice"])
        else:
            cond = Or(x[i] == city_to_index["Nice"], And(x[i-1] == city_to_index["Nice"], x[i] != city_to_index["Nice"]))
            nice_in_period.append(cond)
    s.add(Or(nice_in_period))
    
    frankfurt_in_period = []
    for i in range(18, 20):
        if i == 0:
            cond = (x[0] == city_to_index["Frankfurt"])
        else:
            cond = Or(x[i] == city_to_index["Frankfurt"], And(x[i-1] == city_to_index["Frankfurt"], x[i] != city_to_index["Frankfurt"]))
        frankfurt_in_period.append(cond)
    s.add(Or(frankfurt_in_period))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            city_idx = model.evaluate(x[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()