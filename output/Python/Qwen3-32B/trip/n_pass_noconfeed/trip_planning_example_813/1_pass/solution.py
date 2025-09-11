import itertools
import json

def main():
    cities = {
        'Vilnius': 3,
        'Frankfurt': 5,
        'Stuttgart': 3,
        'London': 2,
        'Santorini': 2,
        'Dublin': 3,
        'Seville': 5
    }
    direct_flights = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'London': ['Frankfurt', 'Santorini', 'Stuttgart', 'Dublin'],
        'Dublin': ['Frankfurt', 'London', 'Seville'],
        'Santorini': ['London'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin']
    }
    city_list = list(cities.keys())
    
    for perm in itertools.permutations(city_list):
        valid = True
        # Check if all transitions are direct flights
        for i in range(len(perm)-1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in direct_flights[current]:
                valid = False
                break
        if not valid:
            continue
        
        # Calculate day ranges
        current_start = 1
        itinerary_data = []
        for city in perm:
            duration = cities[city]
            end = current_start + duration - 1
            itinerary_data.append( (city, current_start, end) )
            current_start = end  # next city starts on this day
        
        # Check total days is 17
        if itinerary_data[-1][2] != 17:
            continue
        
        # Check Stuttgart's stay includes days 7-9
        stuttgart_found = False
        for city, start, end in itinerary_data:
            if city == 'Stuttgart':
                if 6 <= start <= 8:
                    stuttgart_found = True
                break
        if not stuttgart_found:
            continue
        
        # Check London's stay includes day 9 or 10
        london_found = False
        for city, start, end in itinerary_data:
            if city == 'London':
                if start <= 10 and end >= 9:
                    london_found = True
                break
        if not london_found:
            continue
        
        # Found valid itinerary
        itinerary = []
        for city, start, end in itinerary_data:
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # If no itinerary found (should not happen)
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()