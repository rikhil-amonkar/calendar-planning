travel_times = {
    'Bayview': {'Midtown': 30, 'Downtown': 45},
    'Midtown': {'Bayview': 30, 'Downtown': 15, 'Uptown': 30},
    'Downtown': {'Bayview': 45, 'Midtown': 15, 'Uptown': 45},
    'Uptown': {'Midtown': 30, 'Downtown': 45}
}

constraints = {
    'Alice': {'location': 'Midtown', 'start': '10:00', 'end': '12:00', 'min_duration': 30},
    'Bob': {'location': 'Downtown', 'start': '11:00', 'end': '13:00', 'min_duration': 45},
    'Charlie': {'location': 'Uptown', 'start': '10:30', 'end': '12:30', 'min_duration': 30}
}