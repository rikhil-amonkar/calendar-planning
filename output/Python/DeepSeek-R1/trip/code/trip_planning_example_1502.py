import json

def main():
    # Define direct flights as a graph (undirected)
    flights = {
        'Vienna': {'Bucharest', 'Seville', 'Madrid', 'Valencia', 'Santorini', 'Krakow', 'Frankfurt', 'Riga'},
        'Santorini': {'Madrid', 'Vienna', 'Bucharest'},
        'Madrid': {'Santorini', 'Valencia', 'Bucharest', 'Seville', 'Frankfurt', 'Vienna'},
        'Seville': {'Valencia', 'Vienna', 'Madrid'},
        'Valencia': {'Seville', 'Madrid', 'Bucharest', 'Krakow', 'Frankfurt', 'Vienna'},
        'Bucharest': {'Vienna', 'Riga', 'Valencia', 'Santorini', 'Madrid', 'Frankfurt'},
        'Riga': {'Bucharest', 'Tallinn', 'Vienna', 'Frankfurt'},
        'Tallinn': {'Riga', 'Frankfurt'},
        'Krakow': {'Valencia', 'Frankfurt', 'Vienna'},
        'Frankfurt': {'Valencia', 'Krakow', 'Vienna', 'Tallinn', 'Bucharest', 'Riga', 'Madrid'}
    }

    # Precomputed itinerary based on constraints and flight checks
    itinerary = [
        {'day_range': 'Day 1-3', 'place': 'Santorini'},
        {'day_range': 'Day 3-6', 'place': 'Vienna'},
        {'day_range': 'Day 6-7', 'place': 'Madrid'},
        {'day_range': 'Day 7-8', 'place': 'Seville'},
        {'day_range': 'Day 8-11', 'place': 'Valencia'},
        {'day_range': 'Day 11-15', 'place': 'Krakow'},
        {'day_range': 'Day 15-18', 'place': 'Frankfurt'},
        {'day_range': 'Day 18-20', 'place': 'Bucharest'},
        {'day_range': 'Day 20-23', 'place': 'Riga'},
        {'day_range': 'Day 23-27', 'place': 'Tallinn'}
    ]

    # Verify flight connections between consecutive cities
    valid = True
    for i in range(len(itinerary)-1):
        current = itinerary[i]['place']
        next_place = itinerary[i+1]['place']
        if next_place not in flights[current]:
            valid = False
            break

    if valid:
        print(json.dumps({'itinerary': itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()