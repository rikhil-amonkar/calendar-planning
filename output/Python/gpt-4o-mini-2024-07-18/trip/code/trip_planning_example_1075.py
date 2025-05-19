import json

def plan_trip():
    # Input parameters
    trip_duration = 25
    visit_plan = {
        "Vienna": {"days": 4, "fixed": True},
        "Lyon": {"days": 3, "fixed": False},
        "Edinburgh": {"days": 4, "fixed": True, "during_show": True},
        "Reykjavik": {"days": 5, "fixed": False},
        "Stuttgart": {"days": 5, "fixed": False},
        "Manchester": {"days": 2, "fixed": False},
        "Split": {"days": 5, "fixed": False, "wedding": True},
        "Prague": {"days": 4, "fixed": False}
    }

    # Annual show in Edinburgh from Day 5 to Day 8
    show_start = 5
    show_end = 8

    # Days allocated
    allocated_days = {
        'total': 0,
        'plan': []
    }

    # England time in Edinburgh for the show
    allocated_days['plan'].append({'day_range': 'Day 1-4', 'place': 'Vienna'})
    allocated_days['total'] += 4

    # After Vienna, we head to Edinburgh
    allocated_days['plan'].append({'flying': 'Day 4-5', 'from': 'Vienna', 'to': 'Edinburgh'})
    
    # In Edinburgh, participate in the show
    allocated_days['plan'].append({'day_range': 'Day 5-8', 'place': 'Edinburgh (Show)'})
    allocated_days['total'] += 4

    # Leaving Edinburgh after the show
    allocated_days['plan'].append({'flying': 'Day 8-9', 'from': 'Edinburgh', 'to': 'Reykjavik'})
    
    # Spend 5 days in Reykjavik
    allocated_days['plan'].append({'day_range': 'Day 9-13', 'place': 'Reykjavik'})
    allocated_days['total'] += 5

    # Travel from Reykjavik to Stuttgart
    allocated_days['plan'].append({'flying': 'Day 13-14', 'from': 'Reykjavik', 'to': 'Stuttgart'})

    # Spend 5 days in Stuttgart
    allocated_days['plan'].append({'day_range': 'Day 14-18', 'place': 'Stuttgart'})
    allocated_days['total'] += 5

    # From Stuttgart to Split for wedding
    allocated_days['plan'].append({'flying': 'Day 18-19', 'from': 'Stuttgart', 'to': 'Split'})

    # Wedding in Split between Day 19 and Day 23
    allocated_days['plan'].append({'day_range': 'Day 19-23', 'place': 'Split (Wedding)'})
    allocated_days['total'] += 5
    
    # Travel from Split to Prague
    allocated_days['plan'].append({'flying': 'Day 23-24', 'from': 'Split', 'to': 'Prague'})

    # Spend 4 days in Prague
    allocated_days['plan'].append({'day_range': 'Day 24-25', 'place': 'Prague'})
    allocated_days['total'] += 4

    # Include the final travel from Prague to Manchester for completion
    allocated_days['plan'].append({'flying': 'Day 25-25', 'from': 'Prague', 'to': 'Manchester'})

    # Complete days
    assert allocated_days['total'] == trip_duration

    # Output the plan in JSON format
    return json.dumps(allocated_days['plan'], indent=4)

if __name__ == "__main__":
    itinerary = plan_trip()
    print(itinerary)