from z3 import *

def main():
    city_names = ["Warsaw", "Riga", "Budapest", "Paris"]
    
    def connected(i, j):
        return Or(
            And(i == 0, Or(j == 1, j == 2, j == 3)),
            And(i == 1, Or(j == 0, j == 3)),
            And(i == 2, Or(j == 0, j == 3)),
            And(i == 3, Or(j == 0, j == 1, j == 2))
        )
    
    BaseCity = [Int(f'BaseCity_{d}') for d in range(1, 18)]
    TravelDest = [Int(f'TravelDest_{d}') for d in range(1, 17)]
    
    s = Solver()
    
    s.add(BaseCity[0] == 0)
    s.add(TravelDest[0] == -1)
    
    for i in range(17):
        s.add(BaseCity[i] >= 0, BaseCity[i] <= 3)
    for i in range(16):
        s.add(TravelDest[i] >= -1, TravelDest[i] <= 3)
        s.add(Or(
            TravelDest[i] == -1,
            And(TravelDest[i] != BaseCity[i], TravelDest[i] >= 0)
        ))
    
    for d in range(1, 17):
        s.add(BaseCity[d] == If(TravelDest[d-1] != -1, TravelDest[d-1], BaseCity[d-1]))
    
    for d in range(2, 17):
        s.add(BaseCity[d] != 0)
    
    for d in range(0, 16):
        s.add(If(
            TravelDest[d] != -1,
            connected(BaseCity[d], TravelDest[d]),
            True
        ))
    
    travel_days = [If(TravelDest[d] != -1, 1, 0) for d in range(0, 16)]
    s.add(Sum(travel_days) == 3)
    
    in_city = {}
    for c in range(4):
        for d in range(1, 18):
            day_idx = d-1
            if d < 17:
                in_city[(c, d)] = Or(
                    BaseCity[day_idx] == c,
                    And(TravelDest[day_idx] != -1, TravelDest[day_idx] == c)
                )
            else:
                in_city[(c, d)] = (BaseCity[day_idx] == c)
    
    total_days = [0]*4
    for c in range(4):
        total = 0
        for d in range(1, 18):
            total += If(in_city[(c, d)], 1, 0)
        s.add(total == [2, 7, 7, 4][c])
    
    for d in range(11, 18):
        s.add(in_city[(1, d)])
    
    for d in range(12, 17):
        s.add(TravelDest[d-1] == -1)
    
    if s.check() == sat:
        m = s.model()
        print("Day-by-Day Itinerary:")
        for d in range(1, 18):
            cities = []
            for c in range(4):
                if m.evaluate(in_city[(c, d)]):
                    cities.append(city_names[c])
            print(f"Day {d}: {', '.join(cities)}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()