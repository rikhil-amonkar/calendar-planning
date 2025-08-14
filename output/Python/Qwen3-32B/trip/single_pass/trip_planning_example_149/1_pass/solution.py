import json
from itertools import permutations

def main():
    total_days = 10
    cities = ['London', 'Santorini', 'Istanbul']
    durations = {'London': 3, 'Santorini': 6, 'Istanbul': 3}
    conference_days = [5, 10]
    direct_flights = {frozenset(['Istanbul', 'London']), frozenset(['London', 'Santorini'])}
    
    def find_valid_itinerary():
        for perm in permutations(cities):
            current_start = 1
            valid = True
            flight_valid = True
            santorini_days = None
            for i, city in enumerate(perm):
                duration = durations[city]
                current_end = current_start + duration - 1
                if current_end > total_days:
                    valid = False
                    break
                if city == 'Santorini':
                    santorini_days = (current_start, current_end)
                current_start = current_end  # next city starts on this day
            if not valid or current_start != total_days:
                continue
            # Check flight connections
            for i in range(len(perm) - 1):
                city_a, city_b = perm[i], perm[i+1]
                if frozenset([city_a, city_b]) not in direct_flights:
                    flight_valid = False
                    break
            if not flight_valid:
                continue
            # Check conference days
            if santorini_days is None:
                continue
            sant_start, sant_end = santorini_days
            if not (sant_start <= 5 <= sant_end and sant_start <= 10 <= sant_end):
                continue
            # Generate itinerary
            current_start = 1
            itinerary = []
            for city in perm:
                duration = durations[city]
                current_end = current_start + duration - 1
                itinerary.append({
                    'day_range': f"Day {current_start}-{current_end}",
                    'place': city
                })
                current_start = current_end
            return itinerary
        return None
    
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()