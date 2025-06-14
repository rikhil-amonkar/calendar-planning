def create_itinerary():
    itinerary = [
        ('Diving', 'Diving'),              # Day 1: Diving all day
        ('Relaxing', 'Relaxing'),          # Day 2: Relaxing all day
        ('Hiking', 'Ziplining'),           # Day 3: Hiking and Ziplining
        ('Beach', 'Beach'),                # Day 4: Beach all day (2 half-days)
        ('Beach', 'Shopping'),             # Day 5: Beach and Shopping
        ('Shopping', 'Sightseeing'),       # Day 6: Shopping and Sightseeing
        ('Kitesurfing', 'Windsurfing'),    # Day 7: Kitesurfing and WindSurfing
        ('Parasailing', 'Hiking')          # Day 8: Parasailing and Hiking
    ]
    # Add 17 more days of Beach in the morning and Hiking in the afternoon
    itinerary.extend([('Beach', 'Hiking')] * 17)
    return itinerary