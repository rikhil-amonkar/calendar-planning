import json

def main():
    cities = {
        'Dublin': {'days': 5},
        'Helsinki': {'days': 3, 'meet': (3, 5)},
        'Riga': {'days': 3},
        'Reykjavik': {'days': 2},
        'Vienna': {'days': 2, 'event': (2, 3)},
        'Tallinn': {'days': 5, 'wedding': (7, 11)}
    }
    
    flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Reykjavik', 'Dublin'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Riga', 'Helsinki', 'Dublin'],
        'Dublin': ['Riga', 'Vienna', 'Reykjavik', 'Tallinn', 'Helsinki']
    }

    itinerary = [
        {'place': 'Reykjavik', 'start': 1, 'end': 2},
        {'place': 'Vienna', 'start': 2, 'end': 3},
        {'place': 'Riga', 'start': 3, 'end': 5},
        {'place': 'Helsinki', 'start': 5, 'end': 7},
        {'place': 'Tallinn', 'start': 7, 'end': 11},
        {'place': 'Dublin', 'start': 11, 'end': 15}
    ]

    def is_valid(itinerary):
        total_days = {}
        for segment in itinerary:
            city = segment['place']
            days = segment['end'] - segment['start'] + 1
            total_days[city] = total_days.get(city, 0) + days
        
        for city, req in cities.items():
            if total_days.get(city, 0) != req['days']:
                return False
        
        prev_city = None
        for seg in itinerary:
            city = seg['place']
            if prev_city and city not in flights[prev_city]:
                return False
            prev_city = city
            
            if city == 'Vienna':
                if not (seg['start'] <= 2 and seg['end'] >= 3):
                    return False
            if city == 'Tallinn':
                if not (seg['start'] <= 7 and seg['end'] >= 11):
                    return False
            if city == 'Helsinki':
                if not (seg['start'] <= 5 and seg['end'] >= 3):
                    return False
        
        return True

    if is_valid(itinerary):
        output = []
        for seg in itinerary:
            start = seg['start']
            end = seg['end']
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            output.append({'day_range': day_range, 'place': seg['place']})
        print(json.dumps({'itinerary': output}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()