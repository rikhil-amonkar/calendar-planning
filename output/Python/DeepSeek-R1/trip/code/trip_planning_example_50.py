import json

def main():
    required_days = {
        'Vilnius': 4,
        'Munich': 3,
        'Mykonos': 7
    }
    total_days = 12
    possible_sequences = [
        ['Vilnius', 'Munich', 'Mykonos'],
        ['Mykonos', 'Munich', 'Vilnius']
    ]
    
    for seq in possible_sequences:
        first = seq[0]
        second = seq[1]
        third = seq[2]
        
        t1 = required_days[first]
        t2 = t1 + required_days[second] - 1
        days_third = (total_days - t2) + 1
        
        if days_third == required_days[third]:
            itinerary = [
                {"day_range": f"Day 1-{t1}", "place": first},
                {"day_range": f"Day {t1}-{t2}", "place": second},
                {"day_range": f"Day {t2}-{total_days}", "place": third}
            ]
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()