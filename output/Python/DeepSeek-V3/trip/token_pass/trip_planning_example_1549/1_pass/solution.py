import json
from itertools import permutations
from collections import defaultdict

def find_valid_itinerary():
    # Cities and required days
    cities = {
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    # Direct flights (bidirectional unless specified)
    direct_flights = {
        'Riga': ['Prague', 'Milan', 'Tallinn', 'Warsaw', 'Stockholm', 'Lisbon'],
        'Stockholm': ['Milan', 'Lisbon', 'Santorini', 'Warsaw', 'Prague', 'Tallinn', 'Riga'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Santorini', 'Warsaw'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Milan', 'Riga'],
        'Naples': ['Warsaw', 'Milan', 'Lisbon', 'Santorini'],
        'Warsaw': ['Naples', 'Lisbon', 'Stockholm', 'Riga', 'Tallinn', 'Milan', 'Prague', 'Porto'],
        'Prague': ['Riga', 'Tallinn', 'Lisbon', 'Milan', 'Stockholm', 'Warsaw'],
        'Tallinn': ['Riga', 'Prague', 'Warsaw', 'Stockholm'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Santorini': ['Stockholm', 'Milan', 'Naples']
    }
    
    # Make sure all flights are bidirectional
    for city, destinations in list(direct_flights.items()):
        for dest in destinations:
            if dest not in direct_flights:
                direct_flights[dest] = []
            if city not in direct_flights[dest]:
                direct_flights[dest].append(city)
    
    # Hard constraints
    constraints = [
        ('Tallinn', 18, 20),  # Must be in Tallinn between day 18-20
        ('Milan', 24, 26),    # Must be in Milan between day 24-26
        ('Riga', 5, 8)        # Must be in Riga between day 5-8
    ]
    
    # Total days
    total_days = 28
    
    # Try different orders of visiting cities
    city_list = list(cities.keys())
    
    # We'll use a backtracking approach
    def backtrack(current_city, day, visited, itinerary, remaining_days):
        # Base case: if we've used all days and visited all cities
        if day > total_days:
            if len(visited) == len(cities) and all(remaining_days[city] == 0 for city in cities):
                return itinerary[:]
            return None
        
        # Check if we can stay in current city
        if remaining_days[current_city] > 0:
            # Check constraints for current day
            valid = True
            for city, start, end in constraints:
                if day >= start and day <= end and current_city != city:
                    valid = False
                    break
            
            if valid:
                # Stay one more day in current city
                remaining_days[current_city] -= 1
                visited.add(current_city)
                
                # Update itinerary
                if itinerary and itinerary[-1]['place'] == current_city:
                    itinerary[-1]['day_range'] = f"Day {itinerary[-1]['day_range'].split('-')[0].split(' ')[1]}-{day}"
                else:
                    itinerary.append({
                        'day_range': f"Day {day}-{day}",
                        'place': current_city
                    })
                
                # Recurse
                result = backtrack(current_city, day + 1, visited, itinerary, remaining_days)
                if result:
                    return result
                
                # Backtrack
                if itinerary[-1]['place'] == current_city:
                    if itinerary[-1]['day_range'].endswith(f"-{day}"):
                        start_day = int(itinerary[-1]['day_range'].split('-')[0].split(' ')[1])
                        if start_day == day:
                            itinerary.pop()
                        else:
                            itinerary[-1]['day_range'] = f"Day {start_day}-{day-1}"
                remaining_days[current_city] += 1
                if remaining_days[current_city] == cities[current_city]:
                    visited.remove(current_city)
        
        # Try moving to another city
        for next_city in direct_flights[current_city]:
            if next_city == current_city:
                continue
                
            # Check if we need to visit this city
            if remaining_days[next_city] == 0:
                continue
            
            # Check constraints for current day
            valid = True
            for city, start, end in constraints:
                if day >= start and day <= end and next_city != city:
                    valid = False
                    break
            
            if valid:
                # Move to next city (same day counts for both cities)
                # First, if we were in current city, we need to finish that stay
                temp_itinerary = itinerary[:]
                if temp_itinerary and temp_itinerary[-1]['place'] == current_city:
                    start_day = int(temp_itinerary[-1]['day_range'].split('-')[0].split(' ')[1])
                    temp_itinerary[-1]['day_range'] = f"Day {start_day}-{day}"
                
                # Add transition day in next city
                temp_itinerary.append({
                    'day_range': f"Day {day}-{day}",
                    'place': next_city
                })
                
                # Update remaining days for current city (if we were staying there)
                temp_remaining = remaining_days.copy()
                temp_visited = set(visited)
                
                # Spend the day in next city
                temp_remaining[next_city] -= 1
                temp_visited.add(next_city)
                
                # Recurse
                result = backtrack(next_city, day + 1, temp_visited, temp_itinerary, temp_remaining)
                if result:
                    return result
        
        return None
    
    # Try starting from different cities
    for start_city in city_list:
        remaining_days = cities.copy()
        remaining_days[start_city] -= 1
        
        itinerary = [{
            'day_range': f"Day 1-1",
            'place': start_city
        }]
        
        result = backtrack(start_city, 2, {start_city}, itinerary, remaining_days)
        if result:
            return result
    
    return None

def main():
    # Find a valid itinerary
    itinerary = find_valid_itinerary()
    
    if itinerary:
        # Consolidate consecutive days in same city
        consolidated = []
        current = None
        
        for entry in itinerary:
            day_range = entry['day_range']
            place = entry['place']
            start_day = int(day_range.split('-')[0].split(' ')[1])
            end_day = int(day_range.split('-')[1])
            
            if current is None:
                current = {'start': start_day, 'end': end_day, 'place': place}
            elif current['place'] == place:
                current['end'] = end_day
            else:
                consolidated.append({
                    'day_range': f"Day {current['start']}-{current['end']}",
                    'place': current['place']
                })
                current = {'start': start_day, 'end': end_day, 'place': place}
        
        if current:
            consolidated.append({
                'day_range': f"Day {current['start']}-{current['end']}",
                'place': current['place']
            })
        
        # Verify all constraints are met
        cities_visited = defaultdict(int)
        for entry in consolidated:
            place = entry['place']
            day_range = entry['day_range']
            start = int(day_range.split('-')[0].split(' ')[1])
            end = int(day_range.split('-')[1])
            cities_visited[place] += (end - start + 1)
        
        # Check required days
        required_days = {
            'Prague': 5,
            'Tallinn': 3,
            'Warsaw': 2,
            'Porto': 3,
            'Naples': 5,
            'Milan': 3,
            'Lisbon': 5,
            'Santorini': 5,
            'Riga': 4,
            'Stockholm': 2
        }
        
        all_met = True
        for city, days in required_days.items():
            if cities_visited[city] != days:
                print(f"Warning: {city} has {cities_visited[city]} days instead of {days}")
                all_met = False
        
        if all_met:
            print(json.dumps({'itinerary': consolidated}, indent=2))
        else:
            print(json.dumps({'error': 'Could not find valid itinerary meeting all constraints'}, indent=2))
    else:
        print(json.dumps({'error': 'No valid itinerary found'}, indent=2))

if __name__ == "__main__":
    main()