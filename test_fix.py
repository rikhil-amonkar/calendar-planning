from iterative_smt_refinement import evaluate_trip

# Test case 1: Example 1075
test_itinerary_1075 = {
    'itinerary': [
        {'day_range': 'Day 1-5', 'place': 'Stuttgart'},
        {'day_range': 'Day 5', 'place': 'Stuttgart'},
        {'day_range': 'Day 5', 'place': 'Edinburgh'},
        {'day_range': 'Day 5-8', 'place': 'Edinburgh'}
    ]
}

# Test case 2: Example 500
test_itinerary_500 = {
    'itinerary': [
        {'day_range': 'Day 1-7', 'place': 'Hamburg'},
        {'day_range': 'Day 7', 'place': 'Hamburg'},
        {'day_range': 'Day 7', 'place': 'Split'},
        {'day_range': 'Day 7-13', 'place': 'Split'}
    ]
}

# Mock constraints with direct flights
constraints = {
    'direct_flights': [
        {'from': 'Stuttgart', 'to': 'Edinburgh'},
        {'from': 'Hamburg', 'to': 'Split'}
    ]
}

print('Testing Example 1075:')
result_1075, violations_1075 = evaluate_trip(constraints, test_itinerary_1075)
print(f'Result: {result_1075}')
print(f'Violations: {violations_1075}')

print('\nTesting Example 500:')
result_500, violations_500 = evaluate_trip(constraints, test_itinerary_500)
print(f'Result: {result_500}')
print(f'Violations: {violations_500}') 