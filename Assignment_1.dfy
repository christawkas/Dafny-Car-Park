class Car {

    // predicate Valid()
    // {
    //     assume true;
    // }
}


class CarPark {

    var carPark : map<int, Car>;
    var reservations : set<Car>;
    var maxSpots: int;


    // a constructor for the class, setting the car-park up for a new day.
    constructor (x: int)
    {
        maxSpots := x;
    }

    // to allow any car without a reservation to enter the car park.
    method enterCarPark (x: Car) returns (res: bool)
        requires true;
        ensures old(|carPark|+1) <= maxSpots && |carPark|-1 == old(|carPark|);
    {
        
    }

    // to allow any car from any area to leave the car park.
    method leaveCarPark () returns (res: bool)  decreases  carPark
    {

    }

    // to report on the number of non-reserved free spaces currently available.
    method checkAvailability () returns (res: int)  
    {

    }
    
    // to allow a car with a reservation to enter the car park’s reserved area during its hours of operation, or to enter the car park generally outside these hours.
    method enterReservedCarPark (x: Car) returns (res: int)
    {

    }
    
    // to allow a car to be registered as having a reserved space when the owner pays the subscription.
    method makeSubscription (x: Car) returns (res: int)
    {

    }

    // to remove parking restrictions on the reserved spaces (i.e. at 3pm).
    method openReservedArea() returns ()
    {

    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() returns ()
    {

    }
}
method Main ()  
{
    
}
