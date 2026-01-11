import itertools
import json

def find_itinerary():
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    required = {"Krakow": 5, "Frankfurt": 4, "Oslo": 3, "Dubrovnik": 5, "Naples": 5}
    
    direct_flights = {
        ("Dubrovnik", "Oslo"),
        ("Frankfurt", "Krakow"),
        ("Frankfurt", "Oslo"),
        ("Dubrovnik", "Frankfurt"),
        ("Krakow", "Oslo"),
        ("Naples", "Oslo"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Frankfurt"),
        # make undirected
    }
    # make undirected
    direct_flights.update({(b, a) for (a, b) in list(direct_flights)})
    
    # Oslo must be last
    other_cities = [c for c in cities if c != "Oslo"]
    
    for perm in itertools.permutations(other_cities):
        # check direct flights between consecutive
        valid = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in direct_flights:
                valid = False
                break
        if not valid:
            continue
        # check last city connects to Oslo
        if (perm[-1], "Oslo") not in direct_flights:
            continue
        
        # assign days
        # perm = (A,B,C,D)
        a, b, c, d = [required[p] for p in perm]
        # day ranges
        # A: 1..a
        # B: a..a+b-1
        # C: a+b-1..a+b+c-2
        # D: a+b+c-2..a+b+c+d-3
        # Oslo: a+b+c+d-3..a+b+c+d-1
        
        # Dubrovnik constraint: its 5 days must include days 5..9
        # find where Dubrovnik is in perm
        try:
            idx = perm.index("Dubrovnik")
        except ValueError:
            continue
        
        if idx == 0:
            start = 1
            end = a
        elif idx == 1:
            start = a
            end = a + b - 1
        elif idx == 2:
            start = a + b - 1
            end = a + b + c - 2
        elif idx == 3:
            start = a + b + c - 2
            end = a + b + c + d - 3
        
        # check if days 5..9 are within [start, end] (inclusive)
        if not (start <= 5 and end >= 9):
            continue
        
        # Oslo constraint: days 16..18
        oslo_start = a + b + c + d - 3
        if oslo_start != 16:
            continue
        
        # all constraints satisfied
        # build itinerary
        itinerary = []
        day = 1
        for i, city in enumerate(perm):
            dur = required[city]
            if i == 0:
                itinerary.append({"day_range": f"Day {day}-{day+dur-1}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {day}-{day+dur-1}", "place": city})
            day += dur - 1
        # Oslo
        itinerary.append({"day_range": f"Day {day}-{day+2}", "place": "Oslo"})
        
        return {"itinerary": itinerary}
    
    return {"itinerary": []}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result, indent=2))