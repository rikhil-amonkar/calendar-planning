from z3 import *
import json

def main():
    cities = ["Prague", "Brussels", "Riga", "Munich", "Seville", "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"]
    City, city_consts = EnumSort('City', cities)
    Prague, Brussels, Riga, Munich, Seville, Stockholm, Istanbul, Amsterdam, Vienna, Split = city_consts

    direct_flights = [
        ("Riga", "Stockholm"), ("Stockholm", "Brussels"), ("Istanbul", "Munich"), ("Istanbul", "Riga"), 
        ("Prague", "Split"), ("Vienna", "Brussels"), ("Vienna", "Riga"), ("Split", "Stockholm"), 
        ("Munich", "Amsterdam"), ("Split", "Amsterdam"), ("Amsterdam", "Stockholm"), ("Amsterdam", "Riga"), 
        ("Vienna", "Stockholm"), ("Vienna", "Istanbul"), ("Vienna", "Seville"), ("Istanbul", "Amsterdam"), 
        ("Munich", "Brussels"), ("Prague", "Munich"), ("Riga", "Munich"), ("Prague", "Amsterdam"), 
        ("Prague", "Brussels"), ("Prague", "Istanbul"), ("Istanbul", "Stockholm"), ("Vienna", "Prague"), 
        ("Munich", "Split"), ("Vienna", "Amsterdam"), ("Prague", "Stockholm"), ("Brussels", "Seville"), 
        ("Munich", "Stockholm"), ("Istanbul", "Brussels"), ("Amsterdam", "Seville"), ("Vienna", "Split"), 
        ("Munich", "Seville"), ("Riga", "Brussels"), ("Prague", "Riga"), ("Vienna", "Munich")
    ]
    
    flight_set = set()
    for c1_str, c2_str in direct_flights:
        idx1 = cities.index(c1_str)
        idx2 = cities.index(c2_str)
        city1 = city_consts[idx1]
        city2 = city_consts[idx2]
        flight_set.add((city1, city2))
    
    all_pairs = list(flight_set)
    
    loc = [Const('loc_%d' % i, City) for i in range(21)]
    
    s = Solver()
    
    for d in range(1, 21):
        cond = (loc[d-1] != loc[d])
        options = []
        for (c1, c2) in all_pairs:
            options.append(And(loc[d-1] == c1, loc[d] == c2))
            options.append(And(loc[d-1] == c2, loc[d] == c1))
        s.add(Implies(cond, Or(options)))
    
    total_days = {}
    for city in city_consts:
        total = 0
        for d in range(1, 21):
            total += If(Or(loc[d-1] == city, loc[d] == city), 1, 0)
        total_days[city] = total
    
    s.add(total_days[Prague] == 5)
    for d in [5,6,7,8,9]:
        s.add(Or(loc[d-1] == Prague, loc[d] == Prague))
    
    s.add(total_days[Stockholm] == 2)
    s.add(Or(loc[15] == Stockholm, loc[16] == Stockholm))
    s.add(Or(loc[16] == Stockholm, loc[17] == Stockholm))
    
    s.add(total_days[Riga] == 2)
    s.add(Or(Or(loc[14] == Riga, loc[15] == Riga), Or(loc[15] == Riga, loc[16] == Riga)))
    
    s.add(total_days[Vienna] == 5)
    disj_vienna = []
    for d in [1,2,3,4,5]:
        disj_vienna.append(Or(loc[d-1] == Vienna, loc[d] == Vienna))
    s.add(Or(disj_vienna))
    
    s.add(total_days[Split] == 3)
    disj_split = []
    for d in [11,12,13]:
        disj_split.append(Or(loc[d-1] == Split, loc[d] == Split))
    s.add(Or(disj_split))
    
    s.add(total_days[Brussels] == 2)
    s.add(total_days[Munich] == 2)
    s.add(total_days[Seville] == 3)
    s.add(total_days[Istanbul] == 2)
    s.add(total_days[Amsterdam] == 3)
    
    s.add(loc[4] != Prague)
    s.add(loc[5] == Prague)
    s.add(loc[8] == Prague)
    s.add(loc[9] != Prague)
    
    s.add(loc[14] != Stockholm)
    s.add(loc[15] != Stockholm)
    s.add(loc[16] == Stockholm)
    s.add(loc[17] != Stockholm)
    
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in range(1, 21):
            start_val = m.evaluate(loc[d-1])
            end_val = m.evaluate(loc[d])
            start_name = start_val.decl().name()
            end_name = end_val.decl().name()
            if start_name == end_name:
                cities_list = [start_name]
            else:
                cities_list = sorted([start_name, end_name])
            itinerary_list.append({"day": d, "cities": cities_list})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()