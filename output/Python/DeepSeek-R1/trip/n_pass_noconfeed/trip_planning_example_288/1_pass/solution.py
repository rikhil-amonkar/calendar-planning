import json
import itertools

def main():
    total_days = 15
    cities = {
        "Manchester": {"required_days": 7, "fixed_interval": (1, 7)},
        "Stuttgart": {"required_days": 5, "fixed_interval": (11, 15)},
        "Madrid": {"required_days": 4},
        "Vienna": {"required_days": 2}
    }
    direct_flights = [
        ('Vienna', 'Stuttgart'),
        ('Manchester', 'Vienna'),
        ('Madrid', 'Vienna'),
        ('Manchester', 'Stuttgart'),
        ('Manchester', 'Madrid')
    ]
    
    direct_flights_set = set()
    for a, b in direct_flights:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    fixed_block1_city = "Manchester"
    fixed_block2_city = "Stuttgart"
    fixed_block1_end = cities[fixed_block1_city]["fixed_interval"][1]
    fixed_block2_start = cities[fixed_block2_city]["fixed_interval"][0]
    
    non_fixed_cities = [city for city in cities if "fixed_interval" not in cities[city]]
    valid_permutation = None
    
    for perm in itertools.permutations(non_fixed_cities):
        city1, city2 = perm
        req1 = cities[city1]["required_days"]
        req2 = cities[city2]["required_days"]
        
        start1 = fixed_block1_end
        end1 = start1 + req1 - 1
        start2 = end1
        end2 = start2 + req2 - 1
        
        if end2 != fixed_block2_start:
            continue
        
        flight1 = (fixed_block1_city, city1) in direct_flights_set
        flight2 = (city1, city2) in direct_flights_set
        flight3 = (city2, fixed_block2_city) in direct_flights_set
        
        if flight1 and flight2 and flight3:
            valid_permutation = perm
            break
    
    if valid_permutation is None:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    city1, city2 = valid_permutation
    req1 = cities[city1]["required_days"]
    req2 = cities[city2]["required_days"]
    
    start1 = fixed_block1_end
    end1 = start1 + req1 - 1
    start2 = end1
    end2 = start2 + req2 - 1
    
    itinerary = [
        {"day_range": f"Day {cities['Manchester']['fixed_interval'][0]}-{cities['Manchester']['fixed_interval'][1]}", "place": "Manchester"},
        {"day_range": f"Day {start1}-{end1}", "place": city1},
        {"day_range": f"Day {start2}-{end2}", "place": city2},
        {"day_range": f"Day {cities['Stuttgart']['fixed_interval'][0]}-{cities['Stuttgart']['fixed_interval'][1]}", "place": "Stuttgart"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()