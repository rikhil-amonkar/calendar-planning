from z3 import *

def main():
    City, (Paris, Oslo, Porto, Geneva, Reykjavik) = EnumSort('City', ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik'])
    
    end_city = [Const('end_city_%d' % i, City) for i in range(24)]
    
    s = Solver()
    
    for i in range(0, 7):
        s.add(end_city[i] == Geneva)
    
    for i in range(7, 24):
        s.add(end_city[i] != Geneva)
    
    direct_flights = {
        (Paris, Oslo), (Oslo, Paris),
        (Geneva, Oslo), (Oslo, Geneva),
        (Porto, Paris), (Paris, Porto),
        (Geneva, Paris), (Paris, Geneva),
        (Geneva, Porto), (Porto, Geneva),
        (Paris, Reykjavik), (Reykjavik, Paris),
        (Reykjavik, Oslo), (Oslo, Reykjavik),
        (Porto, Oslo), (Oslo, Porto)
    }
    
    def flight_ok(c1, c2):
        return Or([And(c1 == c1_val, c2 == c2_val) for (c1_val, c2_val) in direct_flights])
    
    for i in range(1, 24):
        c1 = end_city[i-1]
        c2 = end_city[i]
        s.add(If(c1 != c2, flight_ok(c1, c2), True))
    
    total_paris = 0
    total_oslo = 0
    total_porto = 0
    total_geneva = 0
    total_reykjavik = 0
    
    for i in range(1, 24):
        total_paris += If(Or(end_city[i-1] == Paris, end_city[i] == Paris), 1, 0)
        total_oslo += If(Or(end_city[i-1] == Oslo, end_city[i] == Oslo), 1, 0)
        total_porto += If(Or(end_city[i-1] == Porto, end_city[i] == Porto), 1, 0)
        total_geneva += If(Or(end_city[i-1] == Geneva, end_city[i] == Geneva), 1, 0)
        total_reykjavik += If(Or(end_city[i-1] == Reykjavik, end_city[i] == Reykjavik), 1, 0)
    
    s.add(total_paris == 6)
    s.add(total_oslo == 5)
    s.add(total_porto == 7)
    s.add(total_geneva == 7)
    s.add(total_reykjavik == 2)
    
    oslo_presence = []
    for day in [19, 20, 21, 22, 23]:
        oslo_presence.append(Or(end_city[day-1] == Oslo, end_city[day] == Oslo))
    s.add(Or(oslo_presence))
    
    if s.check() == sat:
        m = s.model()
        res = [m[end_city[i]] for i in range(24)]
        
        city_names = {
            Paris: "Paris",
            Oslo: "Oslo",
            Porto: "Porto",
            Geneva: "Geneva",
            Reykjavik: "Reykjavik"
        }
        
        for day in range(1, 24):
            start = res[day-1]
            end = res[day]
            if start == end:
                print(f"Day {day}: Stay in {city_names[start]}")
            else:
                print(f"Day {day}: Travel from {city_names[start]} to {city_names[end]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()