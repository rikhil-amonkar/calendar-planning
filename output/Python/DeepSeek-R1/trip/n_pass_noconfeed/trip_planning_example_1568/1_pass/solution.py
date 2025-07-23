import json

def main():
    # Define the graph of direct flights (bidirectional)
    graph = {
        'Riga': ['Stockholm', 'Istanbul', 'Amsterdam', 'Brussels', 'Munich', 'Prague'],
        'Stockholm': ['Riga', 'Brussels', 'Split', 'Amsterdam', 'Vienna', 'Istanbul', 'Prague', 'Munich'],
        'Brussels': ['Stockholm', 'Vienna', 'Munich', 'Prague', 'Istanbul', 'Riga', 'Seville'],
        'Istanbul': ['Munich', 'Riga', 'Vienna', 'Stockholm', 'Amsterdam', 'Brussels'],
        'Prague': ['Split', 'Munich', 'Amsterdam', 'Brussels', 'Istanbul', 'Riga', 'Stockholm', 'Vienna'],
        'Munich': ['Istanbul', 'Amsterdam', 'Brussels', 'Prague', 'Split', 'Stockholm', 'Seville', 'Riga'],
        'Split': ['Prague', 'Munich', 'Amsterdam', 'Stockholm', 'Vienna'],
        'Amsterdam': ['Munich', 'Split', 'Stockholm', 'Riga', 'Seville', 'Istanbul', 'Vienna'],
        'Vienna': ['Brussels', 'Riga', 'Stockholm', 'Istanbul', 'Seville', 'Prague', 'Split', 'Amsterdam', 'Munich'],
        'Seville': ['Brussels', 'Amsterdam', 'Vienna', 'Munich']
    }
    
    # Define the required days per city
    req_days = {
        'Prague': 5,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Stockholm': 2,
        'Istanbul': 2,
        'Amsterdam': 3,
        'Vienna': 5,
        'Split': 3
    }
    
    # Define the itinerary blocks: (start_day, end_day, city)
    blocks = [
        (1, 5, 'Vienna'),
        (5, 9, 'Prague'),
        (9, 10, 'Munich'),
        (10, 12, 'Split'),
        (12, 14, 'Amsterdam'),
        (14, 15, 'Riga'),
        (15, 16, 'Brussels'),
        (16, 17, 'Stockholm'),
        (17, 18, 'Istanbul'),
        (18, 20, 'Seville')
    ]
    
    # Validate the itinerary
    # Check contiguity
    valid = True
    for i in range(len(blocks) - 1):
        if blocks[i][1] != blocks[i+1][0]:
            valid = False
            break
    
    # Check direct flights
    if valid:
        for i in range(len(blocks) - 1):
            city_a = blocks[i][2]
            city_b = blocks[i+1][2]
            if city_b not in graph[city_a]:
                valid = False
                break
    
    # Check total days per city
    if valid:
        city_days = {}
        for s, e, city in blocks:
            days = e - s + 1
            city_days[city] = city_days.get(city, 0) + days
        
        for city, req in req_days.items():
            if city_days.get(city, 0) != req:
                valid = False
                break
    
    # Check fixed events
    if valid:
        # Prague must be visited from day 5 to 9
        for day in range(5, 10):
            found = False
            for s, e, city in blocks:
                if city == 'Prague' and s <= day <= e:
                    found = True
                    break
            if not found:
                valid = False
                break
        
        # Stockholm must be visited on day 16 and 17
        for day in [16, 17]:
            found = False
            for s, e, city in blocks:
                if city == 'Stockholm' and s <= day <= e:
                    found = True
                    break
            if not found:
                valid = False
                break
        
        # Riga must be visited between day 15 and 16 (inclusive)
        found_riga = False
        for s, e, city in blocks:
            if city == 'Riga':
                for day in range(s, e + 1):
                    if day in [15, 16]:
                        found_riga = True
                        break
                if found_riga:
                    break
        if not found_riga:
            valid = False
        
        # Split must be visited between day 11 and 13 (inclusive)
        found_split = False
        for s, e, city in blocks:
            if city == 'Split':
                for day in range(s, e + 1):
                    if day in [11, 12, 13]:
                        found_split = True
                        break
                if found_split:
                    break
        if not found_split:
            valid = False
        
        # Vienna must be visited between day 1 and 5 (inclusive)
        found_vienna = False
        for s, e, city in blocks:
            if city == 'Vienna':
                for day in range(s, e + 1):
                    if 1 <= day <= 5:
                        found_vienna = True
                        break
                if found_vienna:
                    break
        if not found_vienna:
            valid = False
    
    if not valid:
        print('No valid itinerary found.')
        return
    
    # Format the itinerary for output
    itinerary_list = []
    for block in blocks:
        s, e, city = block
        day_range = f"Day {s}-{e}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()