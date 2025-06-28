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
    remaining_initial['Istanbul'] = 2
    remaining_initial['Vienna'] = 2
    remaining_initial['Riga'] = 1
    remaining_initial['Brussels'] = 2
    remaining_initial['Madrid'] = 2
    remaining_initial['Vilnius'] = 4
    remaining_initial['Venice'] = 5
    remaining_initial['Geneva'] = 4
    remaining_initial['Munich'] = 3
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
    
    # Remove prohibited flights
    direct_flights.discard(('Istanbul', 'Venice'))
    direct_flights.discard(('Venice', 'Istanbul'))

    # Memoization cache
    memo = {}
    
    def dfs(current_city, current_day, remaining, ongoing, itinerary):
        if current_day > 27:
            if all(x == 0 for x in remaining.values()):
                itinerary.append({'start': ongoing, 'end': 27, 'city': current_city})
                return itinerary
            else:
                return None
                
        state = (current_city, current_day, tuple(remaining[city] for city in cities))
        if state in memo:
            return memo[state]
            
        required_city = must_be.get(current_day)
        if required_city is not None:
            if required_city != current_city:
                if (current_city, required_city) in direct_flights and remaining[required_city] > 0:
                    new_remaining = remaining.copy()
                    new_remaining[required_city] -= 1
                    new_itinerary = itinerary + [{'start': ongoing, 'end': current_day-1, 'city': current_city}]
                    result = dfs(required_city, current_day+1, new_remaining, current_day, new_itinerary)
                    memo[state] = result
                    return result
                else:
                    memo[state] = None
                    return None
            else:
                if remaining[current_city] > 0:
                    new_remaining = remaining.copy()
                    new_remaining[current_city] -= 1
                    result = dfs(current_city, current_day+1, new_remaining, ongoing, itinerary)
                    memo[state] = result
                    return result
                else:
                    memo[state] = None
                    return None
        else:
            next_day = current_day + 1
            if next_day <= 27 and next_day in must_be:
                next_required = must_be[next_day]
                if current_city == next_required:
                    if remaining[current_city] > 0:
                        new_remaining = remaining.copy()
                        new_remaining[current_city] -= 1
                        result = dfs(current_city, current_day+1, new_remaining, ongoing, itinerary)
                        memo[state] = result
                        return result
                    else:
                        memo[state] = None
                        return None
                else:
                    if (current_city, next_required) in direct_flights and remaining[next_required] > 0:
                        new_remaining = remaining.copy()
                        new_remaining[next_required] -= 1
                        new_itinerary = itinerary + [{'start': ongoing, 'end': current_day-1, 'city': current_city}]
                        result = dfs(next_required, current_day+1, new_remaining, current_day, new_itinerary)
                        memo[state] = result
                        return result
                    else:
                        memo[state] = None
                        return None
            else:
                if remaining[current_city] > 0:
                    new_remaining = remaining.copy()
                    new_remaining[current_city] -= 1
                    result = dfs(current_city, current_day+1, new_remaining, ongoing, itinerary)
                    if result is not None:
                        memo[state] = result
                        return result
                for next_city in cities:
                    if next_city == current_city:
                        continue
                    if (current_city, next_city) in direct_flights and remaining[next_city] > 0:
                        new_remaining = remaining.copy()
                        new_remaining[next_city] -= 1
                        new_itinerary = itinerary + [{'start': ongoing, 'end': current_day-1, 'city': current_city}]
                        result = dfs(next_city, current_day+1, new_remaining, current_day, new_itinerary)
                        if result is not None:
                            memo[state] = result
                            return result
                memo[state] = None
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