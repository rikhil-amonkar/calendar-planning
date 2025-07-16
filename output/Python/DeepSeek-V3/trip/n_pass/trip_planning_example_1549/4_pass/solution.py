import json
from collections import deque

def main():
    # Define city stay durations (minimum days)
    city_durations = {
        'Prague': 3,
        'Tallinn': 2,
        'Warsaw': 2,
        'Porto': 2,
        'Naples': 3,
        'Milan': 2,
        'Lisbon': 3,
        'Santorini': 3,
        'Riga': 3,
        'Stockholm': 2
    }
    
    # Define direct flights (fixed typos in city names)
    flights = {
        'Riga': ['Prague', 'Milan', 'Tallinn', 'Warsaw', 'Stockholm'],
        'Stockholm': ['Milan', 'Lisbon', 'Santorini', 'Warsaw', 'Prague', 'Tallinn', 'Riga'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Warsaw', 'Santorini'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Milan', 'Riga'],
        'Naples': ['Warsaw', 'Milan', 'Santorini', 'Lisbon'],
        'Warsaw': ['Naples', 'Lisbon', 'Porto', 'Tallinn', 'Stockholm', 'Riga', 'Milan', 'Prague'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Prague': ['Riga', 'Tallinn', 'Lisbon', 'Stockholm', 'Milan', 'Warsaw'],
        'Tallinn': ['Riga', 'Prague', 'Warsaw', 'Stockholm'],
        'Santorini': ['Stockholm', 'Milan', 'Naples']
    }
    
    # Corrected city name spellings
    city_name_map = {
        'Milan': 'Milan',
        'Lisbon': 'Lisbon',
        'Prague': 'Prague',
        'Riga': 'Riga',
        'Stockholm': 'Stockholm',
        'Warsaw': 'Warsaw',
        'Porto': 'Porto',
        'Naples': 'Naples',
        'Tallinn': 'Tallinn',
        'Santorini': 'Santorini'
    }
    
    # Function to find shortest path between two cities
    def find_connection(start, end):
        if end in flights[start]:
            return []
        
        visited = {start}
        queue = deque()
        queue.append((start, []))
        
        while queue:
            city, path = queue.popleft()
            for neighbor in flights[city]:
                if neighbor == end:
                    return path + [neighbor]
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        return None
    
    # Create initial itinerary with minimum durations
    cities_to_visit = ['Prague', 'Riga', 'Warsaw', 'Stockholm', 'Lisbon', 'Tallinn', 'Porto', 'Milan', 'Naples']
    itinerary = []
    current_day = 1
    
    for i in range(len(cities_to_visit)-1):
        current_city = cities_to_visit[i]
        next_city = cities_to_visit[i+1]
        
        # Add current city to itinerary
        duration = city_durations[current_city]
        itinerary.append({
            'day_range': f'Day {current_day}-{current_day + duration - 1}',
            'place': current_city
        })
        current_day += duration
        
        # Check if direct flight exists
        if next_city not in flights[current_city]:
            # Find connecting path
            connection = find_connection(current_city, next_city)
            if connection:
                # Add 1-day stopovers for connecting cities
                for stopover in connection[:-1]:
                    itinerary.append({
                        'day_range': f'Day {current_day}-{current_day}',
                        'place': stopover
                    })
                    current_day += 1
    
    # Add the last city
    last_city = cities_to_visit[-1]
    duration = city_durations[last_city]
    itinerary.append({
        'day_range': f'Day {current_day}-{current_day + duration - 1}',
        'place': last_city
    })
    current_day += duration - 1
    
    # Adjust if we exceeded 28 days
    while current_day > 28 and len(itinerary) > 0:
        # Find the longest stay that can be reduced
        longest_stay = max(
            (i for i, item in enumerate(itinerary) if 
             parse_day(item['day_range'].split('-')[1]) - parse_day(item['day_range'].split('-')[0]) + 1 > city_durations[item['place']]),
            key=lambda i: parse_day(itinerary[i]['day_range'].split('-')[1]) - parse_day(itinerary[i]['day_range'].split('-')[0]),
            default=None
        )
        
        if longest_stay is not None:
            # Reduce this stay by 1 day
            item = itinerary[longest_stay]
            start, end = map(parse_day, item['day_range'].split('-'))
            item['day_range'] = f'Day {start}-{end-1}'
            current_day -= 1
            # Adjust subsequent day ranges
            for i in range(longest_stay+1, len(itinerary)):
                start, end = map(parse_day, itinerary[i]['day_range'].split('-'))
                itinerary[i]['day_range'] = f'Day {start-1}-{end-1}'
        else:
            # Can't reduce any stays further, need to remove a city
            break
    
    # Final itinerary
    output = {
        'itinerary': itinerary,
        'total_days': parse_day(itinerary[-1]['day_range'].split('-')[1])
    }
    
    print(json.dumps(output, indent=2))

def parse_day(day_str):
    return int(day_str.replace('Day', '').strip())

if __name__ == '__main__':
    main()