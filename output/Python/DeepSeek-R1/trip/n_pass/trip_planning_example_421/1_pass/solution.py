import itertools
import json

def main():
    cities = {
        "Nice": {"duration": 5},
        "Krakow": {"duration": 6},
        "Dublin": {"duration": 7},
        "Lyon": {"duration": 4},
        "Frankfurt": {"duration": 2}
    }
    
    flights_graph = {
        "Nice": ["Dublin", "Frankfurt", "Lyon"],
        "Dublin": ["Nice", "Frankfurt", "Krakow", "Lyon"],
        "Krakow": ["Dublin", "Frankfurt"],
        "Frankfurt": ["Dublin", "Krakow", "Lyon", "Nice"],
        "Lyon": ["Frankfurt", "Dublin", "Nice"]
    }
    
    remaining_cities = ["Lyon", "Dublin", "Krakow"]
    
    valid_permutation = None
    for perm in itertools.permutations(remaining_cities):
        if perm[0] not in flights_graph["Nice"]:
            continue
        if perm[2] not in flights_graph["Frankfurt"]:
            continue
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1] not in flights_graph[perm[i]]:
                valid = False
                break
        if valid:
            valid_permutation = perm
            break
            
    if valid_permutation is None:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary_blocks = []
    itinerary_blocks.append({"place": "Nice", "start": 1, "end": 5})
    current_day = 5
    for city in valid_permutation:
        duration = cities[city]["duration"]
        end_day = current_day + duration - 1
        itinerary_blocks.append({"place": city, "start": current_day, "end": end_day})
        current_day = end_day
        
    itinerary_blocks.append({"place": "Frankfurt", "start": 19, "end": 20})
    
    result = {"itinerary": []}
    for block in itinerary_blocks:
        day_range_str = f"Day {block['start']}-{block['end']}"
        result["itinerary"].append({"day_range": day_range_str, "place": block["place"]})
        
    print(json.dumps(result))

if __name__ == "__main__":
    main()