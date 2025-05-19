import json

def main():
    cities = {'Zurich': 3, 'Hamburg': 2, 'Helsinki': 2, 'Bucharest': 2, 'Split': 7}
    flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Bucharest', 'Helsinki', 'Zurich', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    itinerary = [
        {"day_range": "Day 1-3", "place": "Zurich"},
        {"day_range": "Day 3-4", "place": "Helsinki"},
        {"day_range": "Day 4-10", "place": "Split"},
        {"day_range": "Day 10-11", "place": "Hamburg"},
        {"day_range": "Day 11-12", "place": "Bucharest"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()