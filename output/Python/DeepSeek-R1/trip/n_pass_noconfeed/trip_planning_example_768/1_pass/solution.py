import itertools
import json

def main():
    days = {
        'Mykonos': 4,
        'London': 2,
        'Copenhagen': 3,
        'Tallinn': 4,
        'Oslo': 5,
        'Nice': 3
    }
    
    direct_flights = {
        'London': ['Copenhagen', 'Mykonos', 'Nice', 'Oslo'],
        'Copenhagen': ['London', 'Tallinn', 'Nice', 'Oslo'],
        'Tallinn': ['Copenhagen', 'Oslo'],
        'Mykonos': ['London', 'Nice'],
        'Oslo': ['Tallinn', 'Nice', 'London', 'Copenhagen'],
        'Nice': ['Oslo', 'London', 'Mykonos', 'Copenhagen']
    }
    
    cities_without_nice = ['Mykonos', 'London', 'Copenhagen', 'Tallinn', 'Oslo']
    found = False
    itinerary_segments = None
    perm_used = None
    
    for perm in itertools.permutations(cities_without_nice):
        valid = True
        for i in range(len(perm)-1):
            city1 = perm[i]
            city2 = perm[i+1]
            if city2 not in direct_flights[city1]:
                valid = False
                break
        if valid:
            last_city = perm[-1]
            if 'Nice' not in direct_flights[last_city]:
                valid = False
            else:
                oslo_index = perm.index('Oslo') if 'Oslo' in perm else -1
                if oslo_index < 0:
                    valid = False
                else:
                    if oslo_index in [0, 1]:
                        valid = False
                    elif oslo_index == 2:
                        total_first_three = days[perm[0]] + days[perm[1]] + days[perm[2]]
                        if total_first_three - 2 < 10:
                            valid = False
        if valid:
            found = True
            perm_used = perm
            break
    
    if not found:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    segments = list(perm_used) + ['Nice']
    itinerary = []
    current_end = 0
    for i, city in enumerate(segments):
        length = days[city]
        if i == 0:
            start = 1
            end = start + length - 1
        else:
            start = current_end
            end = start + length - 1
        current_end = end
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()