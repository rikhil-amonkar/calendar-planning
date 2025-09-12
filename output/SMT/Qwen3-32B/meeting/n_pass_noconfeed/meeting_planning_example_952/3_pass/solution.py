travel_times = {
    ('A', 'B'): 10,
    ('B', 'C'): 20
}

print(get_travel_time(travel_times, 'A', 'B'))  # Output: 10
print(get_travel_time(travel_times, 'B', 'A'))  # Output: 10