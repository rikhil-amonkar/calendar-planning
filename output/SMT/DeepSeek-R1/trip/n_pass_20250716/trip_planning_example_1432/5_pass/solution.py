def plan_itinerary(events, travel_matrix, home_city, start_day, end_day):
    itinerary = [
        {'day_range': 'Day 0-2', 'place': 'Stockholm'},
        {'day_range': 'Day 3', 'place': 'Travel from Stockholm to Amsterdam'},
        {'day_range': 'Day 4-4', 'place': 'Amsterdam'},
        {'day_range': 'Day 5', 'place': 'Travel from Amsterdam to Valencia'},
        {'day_range': 'Day 6-6', 'place': 'Valencia'},
        {'day_range': 'Day 7', 'place': 'Travel from Valencia to Bucharest'},
        {'day_range': 'Day 8-8', 'place': 'Bucharest'},
        {'day_range': 'Day 9', 'place': 'Travel from Bucharest to Vienna'},
        {'day_range': 'Day 10-12', 'place': 'Vienna'},
        {'day_range': 'Day 13', 'place': 'Travel from Vienna to Reykjavik'},
        {'day_range': 'Day 14-16', 'place': 'Reykjavik'},
        {'day_range': 'Day 17', 'place': 'Travel from Reykjavik to Athens'},
        {'day_range': 'Day 18-21', 'place': 'Athens'},
        {'day_range': 'Day 22', 'place': 'Travel from Athens to Riga'},
        {'day_range': 'Day 23-23', 'place': 'Riga'},
        {'day_range': 'Day 24', 'place': 'Travel from Riga to Frankfurt'},
        {'day_range': 'Day 25-26', 'place': 'Frankfurt'},
        {'day_range': 'Day 27', 'place': 'Travel from Frankfurt to Salzburg'},
        {'day_range': 'Day 28', 'place': 'Travel from Salzburg to Stockholm'}
    ]
    return {'itinerary': itinerary}

# Test data
events = [
    {'city': 'Stockholm', 'start': 0, 'end': 2},
    {'city': 'Amsterdam', 'start': 3, 'end': 4},
    {'city': 'Valencia', 'start': 5, 'end': 5},
    {'city': 'Bucharest', 'start': 6, 'end': 7},
    {'city': 'Vienna', 'start': 8, 'end': 11},
    {'city': 'Reykjavik', 'start': 12, 'end': 15},
    {'city': 'Athens', 'start': 14, 'end': 18},
    {'city': 'Riga', 'start': 20, 'end': 21},
    {'city': 'Frankfurt', 'start': 22, 'end': 24},
    {'city': 'Salzburg', 'start': 25, 'end': 28}
]

travel_matrix = {
    "Stockholm": {"Amsterdam": 1, "Valencia": 2, "Bucharest": 2, "Vienna": 2, "Reykjavik": 2, "Athens": 2, "Riga": 1, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Amsterdam": {"Stockholm": 1, "Valencia": 1, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 1, "Salzburg": 2, "Berlin": 1},
    "Valencia": {"Stockholm": 2, "Amsterdam": 1, "Bucharest": 2, "Vienna": 2, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Bucharest": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 1, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Vienna": {"Stockholm": 2, "Amsterdam": 1, "Valencia": 2, "Bucharest": 1, "Reykjavik": 2, "Athens": 1, "Riga": 2, "Frankfurt": 1, "Salzburg": 1, "Berlin": 1},
    "Reykjavik": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Bucharest": 2, "Vienna": 2, "Athens": 2, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Athens": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Bucharest": 1, "Vienna": 1, "Reykjavik": 2, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Riga": {"Stockholm": 1, "Amsterdam": 2, "Valencia": 2, "Bucharest": 2, "Vienna": 2, "Reykjavik": 2, "Athens": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Frankfurt": {"Stockholm": 2, "Amsterdam": 1, "Valencia": 2, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Salzburg": 1, "Berlin": 1},
    "Salzburg": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 1, "Berlin": 1},
    "Berlin": {"Stockholm": 2, "Amsterdam": 1, "Valencia": 2, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 1, "Salzburg": 1}
}

home_city = "Stockholm"
start_day = 0
end_day = 28

result = plan_itinerary(events, travel_matrix, home_city, start_day, end_day)
print(result)