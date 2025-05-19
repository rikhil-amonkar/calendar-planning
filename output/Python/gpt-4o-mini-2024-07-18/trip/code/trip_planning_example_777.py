import json

def create_itinerary():
    days_total = 15
    
    # Define the stay durations
    stay_durations = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }

    # Define constraints
    constraints = {
        'Helsinki': {'meet_friends_days': (3, 5)},
        'Vienna': {'show_days': (2, 3)},
        'Tallinn': {'wedding_days': (7, 11)}
    }

    # Define the route
    itinerary = []

    # 1. Dublin for 5 days
    itinerary.append({'day_range': 'Day 1-5', 'place': 'Dublin'})
    
    # 2. Fly to Helsinki for 3 days
    itinerary.append({'flying': 'Day 5-5', 'from': 'Dublin', 'to': 'Helsinki'})
    itinerary.append({'day_range': 'Day 5-8', 'place': 'Helsinki'})

    # 3. Fly to Riga for 3 days (meet friends between Day 3 and 5)
    itinerary.append({'flying': 'Day 8-8', 'from': 'Helsinki', 'to': 'Riga'})
    itinerary.append({'day_range': 'Day 8-11', 'place': 'Riga'})

    # 4. Fly to Tallinn for wedding (Day 7-11)
    itinerary.append({'flying': 'Day 11-11', 'from': 'Riga', 'to': 'Tallinn'})
    itinerary.append({'day_range': 'Day 11-15', 'place': 'Tallinn'})
    
    # 5. Fly to Vienna for 2 days (Day 2-3 show)
    itinerary.append({'flying': 'Day 15-15', 'from': 'Tallinn', 'to': 'Vienna'})
    itinerary.append({'day_range': 'Day 15-16', 'place': 'Vienna'})

    # 6. Fly to Reykjavik for 2 days
    itinerary.append({'flying': 'Day 16-16', 'from': 'Vienna', 'to': 'Reykjavik'})
    itinerary.append({'day_range': 'Day 16-18', 'place': 'Reykjavik'})

    return itinerary

def main():
    itinerary = create_itinerary()
    json_output = json.dumps(itinerary, indent=4)
    print(json_output)

if __name__ == "__main__":
    main()