# Define a function to calculate the area of a rectangle
def calculate_area(length, width):
    return length * width

# Define a function to calculate the perimeter of a rectangle
def calculate_perimeter(length, width):
    return 2 * (length + width)

# Define a main function to test the other functions
def main():
    # Test the calculate_area function
    area = calculate_area(5, 3)
    print(f"The area of the rectangle is {area}")

    # Test the calculate_perimeter function
    perimeter = calculate_perimeter(5, 3)
    print(f"The perimeter of the rectangle is {perimeter}")

# Run the main function if this script is run directly
if __name__ == "__main__":
    main()