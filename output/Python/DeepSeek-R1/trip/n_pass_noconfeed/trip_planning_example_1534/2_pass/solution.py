import json
import itertools

def main():
    cities = {
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Paris': 2,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    fixed_events = [
        {'place': 'Paris', 'start': 1, 'end': 2},
        {'place': 'Barcelona', 'start': 2, 'end': 6},
        {'place': 'Hamburg', 'start': 19, 'end': 22},
        {'place': 'Salzburg', 'start': 22, 'end': 25}
    ]
    
    direct_flights = {
        'Paris': ['Venice', 'Barcelona', 'Hamburg', 'Vilnius', 'Amsterdam', 'Florence', 'Warsaw', 'Tallinn'],
        'Barcelona': ['Amsterdam', 'Warsaw', 'Hamburg', 'Florence', 'Venice', 'Tallinn'],
        'Amsterdam': ['Barcelona', 'Warsaw', 'Vilnius', 'Hamburg', 'Venice', 'Tallinn'],
        'Warsaw': ['Barcelona', 'Amsterdam', 'Venice', 'Vilnius', 'Hamburg', 'Tallinn'],
        'Venice': ['Paris', 'Barcelona', 'Warsaw', 'Amsterdam', 'Hamburg'],
        'Vilnius': ['Amsterdam', 'Paris', 'Warsaw', 'Tallinn'],
        'Hamburg': ['Barcelona', 'Amsterdam', 'Paris', 'Venice', 'Warsaw', 'Salzburg'],
        'Florence': ['Barcelona', 'Paris', 'Amsterdam'],
        'Tallinn': ['Barcelona', 'Amsterdam', 'Paris', 'Warsaw', 'Vilnius'],
        'Salzburg': ['Hamburg']
    }
    
    flexible_cities = ['Warsaw', 'Venice', 'Vilnius', 'Tallinn', 'Florence', 'Amsterdam']
    city_durations = {city: cities[city] for city in flexible_cities}
    
    # Generate base set without Tallinn
    base_set = [city for city in flexible_cities if city != 'Tallinn']
    subsets_list = []
    # Generate all subsets of base_set and add Tallinn
    for r in range(0, len(base_set) + 1):
        for combo in itertools.combinations(base_set, r):
            subset = list(combo) + ['Tallinn']
            total_duration = sum(city_durations[city] for city in subset)
            if total_duration <= 12:  # Total days must fit in 7-18
                subsets_list.append(subset)
    
    # Check each subset and its permutations
    for subset in subsets_list:
        for perm in itertools.permutations(subset):
            # Check flight from Barcelona to first city
            if perm[0] not in direct_flights['Barcelona']:
                continue
            # Check flight from last city to Hamburg
            if 'Hamburg' not in direct_flights[perm[-1]]:
                continue
            # Check consecutive flights
            valid_flight = True
            for i in range(len(perm) - 1):
                if perm[i+1] not in direct_flights[perm[i]]:
                    valid_flight = False
                    break
            if not valid_flight:
                continue
            
            # Schedule the cities
            current_day = 7
            schedule = {}
            for city in perm:
                start = current_day
                end = start + city_durations[city] - 1
                schedule[city] = (start, end)
                current_day = end + 1
            
            # Check Tallinn covers day 11 or 12
            tallinn_start, tallinn_end = schedule['Tallinn']
            if not (tallinn_start <= 11 <= tallinn_end or tallinn_start <= 12 <= tallinn_end):
                continue
            
            # Build itinerary
            itinerary = []
            itinerary.append({'day_range': "Day 1-2", 'place': 'Paris'})
            itinerary.append({'day_range': "Day 2-6", 'place': 'Barcelona'})
            
            for city in perm:
                start, end = schedule[city]
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({'day_range': day_range, 'place': city})
            
            itinerary.append({'day_range': "Day 19-22", 'place': 'Hamburg'})
            itinerary.append({'day_range': "Day 22-25", 'place': 'Salzburg'})
            
            print(json.dumps({'itinerary': itinerary}))
            return
    
    # No valid plan found
    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()