def create_itinerary():
    itinerary = [
        ('Diving', 'Diving'),              # Day 1: Diving all day
        ('Relaxing', 'Relaxing'),          # Day 2: Relaxing all day
        ('Hiking', 'Ziplining'),           # Day 3: Hiking and Ziplining
        ('Beach', 'Shopping'),             # Day 4: Beach morning, Shopping afternoon
        ('Sightseeing', 'Beach'),          # Day 5: Sightseeing morning, Beach afternoon
        ('Shopping', 'Beach'),             # Day 6: Shopping morning, Beach afternoon
        ('Kitesurfing', 'Windsurfing'),    # Day 7: Kitesurfing and Windsurfing
        ('Parasailing', 'Sightseeing')     # Day 8: Parasailing and Sightseeing
    ]
    # Add 17 more days of Hiking in the morning and Sightseeing in the afternoon
    itinerary.extend([('Hiking', 'Sightseeing')] * 17)
    return itinerary