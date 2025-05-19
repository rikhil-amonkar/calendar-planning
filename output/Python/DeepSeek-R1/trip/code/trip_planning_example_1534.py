import json

def main():
    cities_order = [
        ("Paris", 2),
        ("Barcelona", 5),
        ("Florence", 5),
        ("Amsterdam", 2),
        ("Tallinn", 2),
        ("Vilnius", 3),
        ("Warsaw", 4),
        ("Venice", 3),
        ("Hamburg", 4),
        ("Salzburg", 4),
    ]
    
    flight_connections = {
        ('Paris', 'Barcelona'),
        ('Barcelona', 'Florence'),
        ('Florence', 'Amsterdam'),
        ('Amsterdam', 'Tallinn'),
        ('Tallinn', 'Vilnius'),
        ('Vilnius', 'Warsaw'),
        ('Warsaw', 'Venice'),
        ('Venice', 'Hamburg'),
        ('Hamburg', 'Salzburg'),
    }
    
    for i in range(len(cities_order) - 1):
        current, next_ = cities_order[i][0], cities_order[i+1][0]
        if (current, next_) not in flight_connections:
            raise ValueError(f"No flight from {current} to {next_}")
    
    itinerary = []
    current_day = 1
    for city, days in cities_order:
        start = current_day
        end = start + days - 1
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end + 1  # Account for same-day transfer
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()