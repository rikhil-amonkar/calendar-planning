import json

def main():
    must_be = {}
    for day in range(1, 5):
        must_be[day] = 'Geneva'
    for day in range(7, 12):
        must_be[day] = 'Venice'
    for day in range(20, 24):
        must_be[day] = 'Vilnius'
    for day in range(26, 28):
        must_be[day] = 'Brussels'
    
    cities = ['Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Vilnius', 'Venice', 'Geneva', 'Munich', 'Reykjavik']
    remaining_initial = {city: 0 for city in cities}
    remaining_initial['Istanbul'] = 4
    remaining_initial['Vienna'] = 4
    remaining_initial['Riga'] = 2
    remaining_initial['Brussels'] = 2
    remaining_initial['Madrid'] = 4
    remaining_initial['Vilnius'] = 4
    remaining_initial['Venice'] = 5
    remaining_initial['Geneva'] = 4
    remaining_initial['Munich'] = 5
    remaining_initial['Reykjavik'] = 2

    flight_strings = [
        "Munich and Vienna", 
        "Istanbul and Brussels", 
        "Vienna and Vilnius", 
        "Madrid and Munich", 
        "Venice and Brussels", 
        "Riga and Brussels", 
        "Geneva and Istanbul", 
        "Munich and Reykjavik", 
        "Vienna and Istanbul", 
        "Riga and Istanbul", 
        "Reykjavik and Vienna", 
        "Venice and Munich", 
        "Madrid and Venice", 
        "Vilnius and Istanbul", 
        "Venice and Vienna", 
        "Venice and Istanbul", 
        "from Reykjavik to Madrid", 
        "from Riga to Munich", 
        "Munich and Istanbul", 
        "Reykjavik and Brussels", 
        "Vilnius and Brussels", 
        "from Vilnius to Munich", 
        "Madrid and Vienna", 
        "Vienna and Riga", 
        "Geneva and Vienna", 
        "Geneva and Brussels", 
        "Geneva and Madrid", 
        "Munich and Brussels", 
        "Madrid and Istanbul", 
        "Geneva and Munich"
    ]
    
    direct_flights = set()
    for s in flight_strings:
        if s.startswith('from'):
            parts = s.split()
            A = parts[1]
            B = parts[3]
            direct_flights.add((A, B))
            direct_flights.add((B, A))
        else:
            parts = s.split(' and ')
            if len(parts) == 2:
                A = parts[0]
                B = parts[1]
                direct_flights.add((A, B))
                direct_flights.add((B, A))
    
    # Remove the prohibited flight
    direct_flights.discard(('Istanbul', 'Venice'))
    direct_flights.discard(('Venice', 'Istanbul'))
    
    def dfs(current_city, current_day, remaining, ongoing, itinerary):
        if current_day > 27:
            if all(x == 0 for x in remaining.values()):
                itinerary.append({'start': ongoing, 'end': 27, 'city': current_city})
                return itinerary
            else:
                return None
                
        if current_day in must_be:
            required_city = must_be[current_day]
        else:
            required_city = None
            
        new_remaining = remaining.copy()
        if new_remaining[current_city] > 0:
            if required_city is None or required_city == current_city:
                new_remaining[current_city] -= 1
                result = dfs(current_city, current_day+1, new_remaining, ongoing, itinerary)
                if result is not None:
                    return result
                new_remaining = remaining.copy()
        
        if required_city is not None:
            if required_city == current_city:
                next_city_list = []
            else:
                next_city_list = [required_city]
        else:
            next_city_list = [city for city in cities if city != current_city]
        
        for next_city in next_city_list:
            if (current_city, next_city) in direct_flights:
                if remaining[next_city] <= 0:
                    continue
                new_remaining = remaining.copy()
                new_remaining[next_city] -= 1
                new_itinerary = itinerary + [{'start': ongoing, 'end': current_day-1, 'city': current_city}]
                result = dfs(next_city, current_day+1, new_remaining, current_day, new_itinerary)
                if result is not None:
                    return result
        return None

    start_city = 'Geneva'
    start_day = 1
    start_ongoing = 1
    start_remaining = remaining_initial.copy()
    start_remaining['Geneva'] -= 1
    start_itinerary = []
    result_itinerary = dfs(start_city, start_day+1, start_remaining, start_ongoing, start_itinerary)
    
    if result_itinerary is None:
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    formatted_itinerary = []
    for stay in result_itinerary:
        start = stay['start']
        end = stay['end']
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        formatted_itinerary.append({"day_range": day_range, "place": stay['city']})
    
    output = {"itinerary": formatted_itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()